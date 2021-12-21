#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.
 * When you hand in, remove the #define DEBUG line. */
// #define DEBUG
#ifdef DEBUG
// #define debug(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define msg(...) printf(__VA_ARGS__)
#else
//#define debug(fmt, ...)
#define msg(...)
#endif

#define __unused __attribute__((unused))

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* !DRIVER */

typedef int32_t word_t; /* Heap is bascially an array of 4-byte words. */

typedef enum {
  FREE = 0,     /* Block is free */
  USED = 1,     /* Block is used */
  PREVFREE = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

static void *first_block;    /* Address of the first block */
static void *byte_past_heap; /* Address past last byte of last block */
static void *last_block;     /* Points at last block */

/* --=[ boundary tag handling ]=-------------------------------------------- */

static inline word_t bt_size(word_t *bt) {
  return *bt & ~(USED | PREVFREE);
}

static inline int bt_used(word_t *bt) {
  return *bt & USED;
}

static inline int bt_free(word_t *bt) {
  return !(*bt & USED);
}

/* Given boundary tag address calculate it's buddy address. */
static inline word_t *bt_footer(word_t *bt) {
  return (void *)bt + bt_size(bt) - sizeof(word_t);
}

/* Given payload pointer returns an address of boundary tag. */
static inline word_t *bt_fromptr(void *ptr) {
  return (word_t *)ptr - 1;
}

/* Creates boundary tag(s) for given block. */
static inline void bt_make(word_t *bt, size_t size, bt_flags flags) {
  *bt = size | flags;
  *(bt_footer(bt)) = *bt;
}

/* Previous block free flag handling for optimized boundary tags. */
static inline bt_flags bt_get_prevfree(word_t *bt) {
  return *bt & PREVFREE;
}

static inline void bt_clr_prevfree(word_t *bt) {
  if (bt)
    *bt &= ~PREVFREE;
}

static inline void bt_set_prevfree(word_t *bt) {
  *bt |= PREVFREE;
}

/* Returns address of payload. */
static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}

/* Returns address of next block or NULL. */
static inline word_t *bt_next(word_t *bt) {
  // printf("\t\t\t\033[3;42;30m{bt_next}\033[0m bt = 0x%lx move by 0x%lx\n",
  // bt, bt_size(bt));
  word_t *next = bt + bt_size(bt) / sizeof(word_t);

  if (next > last_block || next == bt) {
    // printf("\t\t\treturned NULL 0x%lx > 0x%lx\n", next, last_block);
    return NULL;
  }

  return next;
}

/* Returns address of previous block or NULL. */
static inline word_t *bt_prev(word_t *bt) {
  word_t *prev_footer = bt - 1;
  void *prev = bt - bt_size(prev_footer) / sizeof(word_t);
  // printf("\t\t\t\033[3;42;30m{bt_prev}\033[0m [bt] 0x%lx [shift] 0x%lx
  // [prevft] 0x%lx [prevbt] 0x%lx\n", bt, bt_size(prev_footer), prev_footer,
  // prev);

  if (prev < first_block || prev == bt)
    return NULL;

  return prev;
}

/* --=[ miscellanous procedures ]=------------------------------------------ */

static size_t round_up(size_t size) {
  return (size + ALIGNMENT - 1) & -ALIGNMENT;
}

/* Calculates block size incl. header, footer & payload,
 * and aligns it to block boundary (ALIGNMENT). */
static inline size_t blksz(size_t size) {
  return round_up(size + 2 * sizeof(word_t));
}

static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);
  if (ptr == (void *)-1)
    return NULL;
  return ptr;
}

static inline void split(word_t *bt, size_t size) {
  word_t *remain_block_bt = bt + size / sizeof(word_t);
  size_t remaining_size = bt_size(bt) - size;
  bt_make(bt, size, FREE);
  bt_make(remain_block_bt, remaining_size, FREE);

  // printf("\t\033[3;42;30m{split}\033[0m\033[3;45;30m[splitting block]\033[0m
  // [left]0x%lx:0x%lx (size)0x%lx [right]0x%lx:0x%lx (size)0x%lx
  // (rmsz)0x%lx\n", bt, bt_footer(bt), bt_size(bt), remain_block_bt,
  // bt_footer(remain_block_bt), bt_size(remain_block_bt), remaining_size);

  /* We may split last block, then we have to update last_block pointer. */
  if (bt_next(remain_block_bt) ==
      NULL) { // maybe this isn't the best way (or even correct way) to do it
    last_block = remain_block_bt;
  }
  /* alternative way?? (rather invalid)
  if (remain_block_bt > last_block) {
    last_block = remain_block_bt;
  }
  */
}

/* --=[ mm_init ]=---------------------------------------------------------- */

int mm_init(void) {
  // printf("--== it's mm_init time ==--\n");

  void *ptr = mem_sbrk(ALIGNMENT - sizeof(word_t));
  if (!ptr)
    return -1;

  first_block = ptr + ALIGNMENT - sizeof(word_t);
  bt_make(first_block, 0, FREE);

  byte_past_heap = first_block;
  last_block = first_block;

  // printf("0x%lx 0x%lx 0x%lx 0x%lx\n--== initialized ==--\n", ptr,
  // first_block, last_block, byte_past_heap);

  return 0;
}

/* --=[ malloc ]=----------------------------------------------------------- */

#if 1
/* First fit startegy. */
static word_t *find_fit(size_t reqsz) {
  // printf("\t\033[3;42;30m{find_fit}\033[0m\033[3;43;30m[traversing
  // list]\033[0m\n");

  void *ptr = first_block;

  /*
   * Traverse heap block by block
   */
  while (ptr) {
    // printf("\t\tptr = 0x%lx block_size = 0x%lx\n", ptr, bt_size(ptr));
    // printf("\t\tfirst_block = 0x%lx last_block = 0x%lx byte_past_heap =
    // 0x%lx\n", first_block, last_block, byte_past_heap);
    word_t *bt = ptr;

    /*
     * Current block is exactly the same size as reqiested and free, so we can
     * simply return it.
     */
    if ((bt_size(ptr) == reqsz) && bt_free(ptr)) {
      return bt;
    }
    /*
     * Current block is larger than requested size, so we split it into two
     * block -- of `reqsz` bytes and of remaining bytes.
     */
    else if ((bt_size(ptr) > reqsz) && bt_free(ptr)) {
      // TODO split()
      split(ptr, reqsz);
      return ptr;
    }
    /*
     * Current block is too small or used, so we move to the next one.
     */
    else {
      ptr = bt_next(ptr);
      // printf("\t\t\033[3;43;30m[Move to next block]\033[0m next_ptr =
      // 0x%lx\n", ptr);
    }
  }

  /*
   * We haven't found appropriate block in list, so we have to increase heap
   * size by reqsz.
   */
  ptr = mem_sbrk(reqsz);
  bt_make(ptr, reqsz, FREE);
  last_block = ptr;
  byte_past_heap = ptr + reqsz;
  // printf("\033[3;43;30m[Creating new block]\033[0m at 0x%lx ending at 0x%lx
  // of size 0x%lx [byte_past_heap]0x%lx\n", ptr, bt_footer(ptr) + 1,
  // bt_size(ptr), byte_past_heap);

  return ptr;
}
#else
/* Best fit startegy. */
static word_t *find_fit(size_t reqsz) {
}
#endif

void *malloc(size_t size) {

  // printf("--== it's malloc time ==--\n");
  // printf("\033[3;43;30m[mallocing]\033[0m [reqsz]0x%lx ", size);

  size = blksz(size);

  // printf("[rdpsz]0x%lx\n", size);

  word_t *bt = find_fit(size);
  bt_make(bt, bt_size(bt), USED);

  // printf("--== mallocked ==-- at 0x%lx\n\n", bt_payload(bt));

  mm_checkheap(0);

  return bt_payload(bt);
}

/* --=[ free ]=------------------------------------------------------------- */

void free(void *ptr) {
  // printf("--== it's freeing time ==--\n");
  // printf("{free}    [ptr] 0x%lx\n", ptr);

  if (ptr == NULL) {
    // printf("[ptr=NULL]Haha, very funny.\n");
    return;
  }

  void *left_block_footer = 0;
  size_t left_block_size = 0;
  int left_block_free = -1;

  void *right_block_footer = 0;
  size_t right_block_size = 0;
  int right_block_free = -1;

  /* `ptr` points to start of the payload, but we want a pointer to the
   * beginning of entire block. */
  void *bt = ptr - sizeof(word_t);

  // size_t current_block_size = bt_size(bt);
  // bt_make(bt, current_block_size, FREE);

  /* Footer of the previous block is right next to the current block's header.
   */
  void *left_block_header = bt_prev(bt);
  if (left_block_header) {
    left_block_footer = bt_footer(left_block_header);
    left_block_size = bt_size(left_block_header);
    left_block_free = bt_free(left_block_header);
  }
  /* We already can calculate address of the next block's header. */
  void *right_block_header = bt_next(bt);
  if (right_block_header) {
    right_block_footer = bt_footer(right_block_header);
    right_block_size = bt_size(right_block_header);
    right_block_free = bt_free(right_block_header);
  }

  /* Withouth colaescing we don't change current block's bt's. */
  void *new_block_header = bt;
  void *new_block_footer = bt_footer(bt);
  size_t new_block_size = bt_size(bt);
  // printf("[current block] 0x%lx 0x%lx 0x%lx [free?] %d\n", new_block_header,
  // new_block_footer + sizeof(word_t), new_block_size,
  // bt_free(new_block_header)); printf("[left    block] 0x%lx 0x%lx 0x%lx
  // [free?] %d\n", left_block_header, left_block_footer + sizeof(word_t),
  // left_block_size, left_block_free); printf("[right   block] 0x%lx 0x%lx
  // 0x%lx [free?] %d\n", right_block_header, right_block_footer +
  // sizeof(word_t), right_block_size, right_block_free);

  /*
   * COALESCING
   */
  /* We shift new_block_header to the left if left neighbour is free and is
   * inside the heap. */
  if (left_block_footer && bt_free(left_block_footer)) {
    new_block_header = left_block_header;
    new_block_size += bt_size(left_block_header);
  }
  /* We shift new_block_footer to the right if right neighbour is free and is
   * inside the heap. */
  if (right_block_header && bt_free(right_block_header)) {
    new_block_footer = right_block_footer;
    new_block_size += bt_size(right_block_header);
  }
  bt_make(new_block_header, new_block_size, FREE);
  // printf("[freed   block] 0x%lx 0x%lx 0x%lx [free?] %d\n", new_block_header,
  // new_block_footer + sizeof(word_t), new_block_size,
  // bt_free(new_block_header));

  /* We may connect last block with it's left neighbour, then we have to update
   * last_block pointer. */
  if (bt_next(new_block_header) ==
      NULL) { // maybe this isn't the best way (or even correct way) to do it
    last_block = new_block_header;
  }

  // printf("--== freed ==--\n\n");
  mm_checkheap(0);
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.
 **/
void *realloc(void *old_ptr, size_t size) {
  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(size);

  void *new_ptr = malloc(size);

  /* If malloc() fails, the original block is left untouched. */
  if (!new_ptr)
    return NULL;

  /* Copy the old data. */
  void *bt = old_ptr - sizeof(word_t);
  size_t old_size = bt_size(bt);
  if (size < old_size)
    old_size = size;
  memcpy(new_ptr, old_ptr, old_size);

  /* Free the old block. */
  free(old_ptr);

  return new_ptr;
}

/* --=[ calloc ]=----------------------------------------------------------- */

void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);
  if (new_ptr)
    memset(new_ptr, 0, bytes);
  return new_ptr;
}

/* --=[ mm_checkheap ]=----------------------------------------------------- */

void mm_checkheap(int verbose) {

  // printf("\033[2;103;30m--==::: HEAP :::==--\033[0m\n");
  // printf("\033[3;103;30m[first_block] 0x%lx  [last_block] 0x%lx
  // [byte_past_heap] 0x%lx\033[0m\n\n", first_block, last_block,
  // byte_past_heap);

  int block_id = 0;
  void *ptr = first_block;

  /*
   * Traverse heap block by block
   */
  while (ptr) {

    // printf("[id]%d  [hd]0x%lx  [ft]0x%lx  [free]%d  [size]0x%lx\n", block_id,
    // ptr, bt_footer(ptr), bt_free(ptr), bt_size(ptr));

    // ptr = bt_next(ptr);

    word_t *next = ptr + bt_size(ptr);

    if (next > last_block || next == ptr) {
      // printf("\t[next > last_block]0x%lx > 0x%lx [next == ptr]0x%lx ==
      // 0x%lx\n", next, last_block, next, ptr);
      next = NULL;
    }

    if ((first_block - last_block) > 0) {
      // printf("\033[2;101;30m<ERROR>\033[0m [first_block - last_block]0x%lx
      // [first_block]0x%lx [last_block]0x%lx\n", first_block - last_block,
      // first_block, last_block);
      exit(1);
    }

    if ((last_block - byte_past_heap) > 0) {
      // printf("\033[2;101;30m<ERROR>\033[0m [last_block - byte_past_heap]0x%lx
      // [last_block]0x%lx [byte_past_heap]0x%lx\n", last_block -
      // byte_past_heap, last_block, byte_past_heap);
      exit(1);
    }

    ptr = next;
    block_id++;
  }

  // printf("\033[2;103;30m[--==::: HEAPPY END :::==--\033[0m\n\n");
}
