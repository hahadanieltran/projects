#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

static inline void add_to_list(header *p);
static inline void remove_from_list(header *p);
/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  // TODO implement allocation
  // (void) raw_size;
  // assert(false);
  // exit(1);
  // roundup to 8 bytes
  if (raw_size == 0) {
    return NULL;
  }
  size_t size8 = ((raw_size + 7)/MIN_ALLOCATION)*MIN_ALLOCATION;
  assert(size8 < ARENA_SIZE);
  if (size8 < (ALLOC_HEADER_SIZE)) {
    size8 = (ALLOC_HEADER_SIZE);
  }
  // starting list
  int ilist = size8/MIN_ALLOCATION - 1;
  if (ilist > N_LISTS) {
    ilist = N_LISTS - 1;
  }
  header * freelist = &freelistSentinels[ilist];
  for (; ilist < N_LISTS; ilist++) {
    freelist = &freelistSentinels[ilist];
    // test if the list is empty or not
    if (freelist->next != freelist) {
        break;
    }
    else if (ilist == N_LISTS - 1 && get_size(freelist->next) < size8) {
      header *allocate = allocate_chunk(ARENA_SIZE);
      header *lastFence = get_left_header(allocate);
      if (get_header_from_offset(lastFencePost, get_size(lastFencePost)) == lastFence) {
        set_state(lastFence, UNALLOCATED);
        set_size_and_state(lastFencePost, get_size(lastFencePost) + get_size(lastFence) + get_size(allocate), UNALLOCATED);
        add_to_list(lastFencePost);
        header *size = lastFencePost;
        lastFencePost = get_right_header(allocate);
        lastFencePost->left_size = get_size(size);
      }
      else {
        add_to_list(allocate);
        insert_os_chunk(get_left_header(allocate));
        lastFencePost = get_right_header(allocate);
      }
    }
  }
  size_t totalSize = size8 + ALLOC_HEADER_SIZE;
  header * obj = freelist->next;
  //alloc hdr info
  header *alloc_hdr = (header *) ((char *) obj + get_size(obj) - totalSize);
  set_size_and_state(alloc_hdr, totalSize, ALLOCATED);
  // data size
  if (alloc_hdr != obj) {
    alloc_hdr->left_size = get_size(obj)-totalSize;
    // change size of obj in the freelist
    set_size(obj, alloc_hdr->left_size);
  }
  else {
    alloc_hdr->left_size = get_size(get_left_header(alloc_hdr));
    remove_from_list(alloc_hdr);
  }
  // change left size of object right of alloc_hdr
  header *obj3 = get_right_header(alloc_hdr);
  obj3->left_size = totalSize;
  header *obj4 = get_left_header(alloc_hdr);
  if (get_size(obj4) >= ALLOC_HEADER_SIZE && get_state(obj4) == UNALLOCATED) {
    remove_from_list(obj4);
    add_to_list(obj4);
  }
  if (get_state(obj4) != FENCEPOST) {
    header *obj6 = get_header_from_offset(obj4, -obj4->left_size);
    if (get_state(obj6) == UNALLOCATED && get_state(obj4) == UNALLOCATED) {
      remove_from_list(obj6);
      remove_from_list(obj4);
      set_size(obj6, get_size(obj6) + get_size(obj4));
      alloc_hdr->left_size = get_size(obj6);
      add_to_list(obj6);
    }
  }
  return (header *) alloc_hdr->data;
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  // TODO implement deallocation
  // (void) p;
  // assert(false);
  // exit(1);
  if (p == NULL) {
    return;
  }
  header *hdr = ptr_to_header(p);
  if (get_state(hdr) == UNALLOCATED) {
    printf("Double Free Detected\n");
    assert(false);
  }
  header *left = get_left_header(hdr);
  header *right = get_right_header(hdr);
  int ilist;
  if ((get_state(left) == ALLOCATED && get_state(right) == ALLOCATED) ||
      (get_state(left) == ALLOCATED && get_state(right) == FENCEPOST) ||
      (get_state(left) == FENCEPOST && get_state(right) == ALLOCATED) ||
       get_state(left) == FENCEPOST && get_state(right) == FENCEPOST) {
    set_state(hdr, UNALLOCATED);
    add_to_list(hdr);
  }
  else if ((get_state(right) == UNALLOCATED && get_state(left) == ALLOCATED) ||
           (get_state(right) == UNALLOCATED && get_state(left) == FENCEPOST)) {
    set_size_and_state(hdr, get_size(hdr) + get_size(right), UNALLOCATED);
    remove_from_list(right);
    add_to_list(hdr);
    header *rightNext = get_header_from_offset(hdr, get_size(hdr));
    rightNext->left_size = get_size(hdr);
  }
  else if ((get_state(left) == UNALLOCATED && get_state(right) == ALLOCATED) ||
           (get_state(left) == UNALLOCATED && get_state(right) == FENCEPOST)) {
    set_state(hdr, UNALLOCATED);
    set_size(left, get_size(left) + get_size(hdr));
    ilist = (get_size(hdr) - ALLOC_HEADER_SIZE / MIN_ALLOCATION) - 1;
    if (ilist < N_LISTS) {
      remove_from_list(left);
      add_to_list(left);
    }
    right->left_size = get_size(left);
  }
  else {
    set_state(hdr, UNALLOCATED);
    remove_from_list(right);
    set_size(left, get_size(left) + get_size(hdr) + get_size(right));
    ilist = ((get_size(left) - ALLOC_HEADER_SIZE) / MIN_ALLOCATION) - 1;
    if (ilist < N_LISTS) {
      add_to_list(left);
    }
    header *rightNext = get_header_from_offset(right, get_size(right));
    rightNext->left_size = get_size(left);
  }
}
static inline void add_to_list(header *p) {
  int ilist = ((get_size(p) - ALLOC_HEADER_SIZE) / MIN_ALLOCATION) - 1;
  if (ilist > N_LISTS) {
    ilist = N_LISTS - 1;
  }
  header *freelist = &freelistSentinels[ilist];
  header * ps = freelist;
  if (ps->next != freelist) {
    header *pss = ps->next;
    freelist->next = p;
    p->next = pss;
    p->prev = freelist;
    pss->prev = p;
  }
  else {
    freelist->next = p;
    freelist->prev = p;
    p->next = freelist;
    p->prev = freelist;
  }
}

static inline void remove_from_list(header *p) {
  p->prev->next = p->next;
  p->next->prev = p->prev;
}
/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
