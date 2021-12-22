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
#define DEBUG
#ifdef DEBUG
// #define debug(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define msg(...) printf(__VA_ARGS__)
#else
#define debug(fmt, ...)
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
#ifdef DEBUG
  printf("\t\t\t\033[3;42;30m{bt_next}\033[0m bt = 0x%p move by 0x%x\n", bt,
         bt_size(bt));
#endif
  word_t *next = bt + bt_size(bt) / sizeof(word_t);

  if (next > (word_t *)last_block || next == bt) {
#ifdef DEBUG
    printf("\033[3;101;30mreturned NULL 0x%p > 0x%p\033[0m\n", next,
           last_block);
#endif
    return NULL;
  }

  return next;
}

/* Returns address of previous block or NULL. */
static inline word_t *bt_prev(word_t *bt) {
  word_t *prev_footer = bt - 1;
  void *prev = bt - bt_size(prev_footer) / sizeof(word_t);
#ifdef DEBUG
  printf("\t\t\t\033[3;42;30m{bt_prev}\033[0m [bt] 0x%p [shift] 0x%x [prevft] "
         "0x%p [prevbt] 0x%p\n",
         bt, bt_size(prev_footer), prev_footer, prev);
#endif
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

static inline void split(word_t *bt, size_t size) {
  word_t *remain_block_bt = bt + size / sizeof(word_t);
  size_t remaining_size = bt_size(bt) - size;
  bt_make(bt, size, FREE);
  bt_make(remain_block_bt, remaining_size, FREE);

#ifdef DEBUG
  printf("\t\033[3;42;30m{split}\033[0m\033[3;45;30m[splitting block]\033[0m "
         "[left]0x%p:0x%p (size)0x%x [right]0x%p:0x%p (size)0x%x (rmsz)0x%lx\n",
         bt, bt_footer(bt), bt_size(bt), remain_block_bt,
         bt_footer(remain_block_bt), bt_size(remain_block_bt), remaining_size);
#endif
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
#ifdef DEBUG
  printf("\033[3;103;30m--== it's mm_init time ==--\033[0m\n");
#endif

  void *ptr = mem_sbrk(ALIGNMENT - sizeof(word_t));
  if (!ptr)
    return -1;

  first_block = ptr + ALIGNMENT - sizeof(word_t);
  bt_make(first_block, 0, FREE);

  byte_past_heap = first_block;
  last_block = first_block;

#ifdef DEBUG
  printf("0x%p 0x%p 0x%p 0x%p\n\033[3;46;30m--== initialized ==--\033[0m\n",
         ptr, first_block, last_block, byte_past_heap);
#endif

  return 0;
}

/* --=[ malloc ]=----------------------------------------------------------- */

#if 1
/* First fit startegy. */
static word_t *find_fit(size_t reqsz) {
#ifdef DEBUG
  printf(
    "\t\033[3;42;30m{find_fit}\033[0m\033[3;43;30m[traversing list]\033[0m\n");
#endif

  void *ptr = first_block;

  /*
   * Traverse heap block by block
   */
  while (ptr) {
#ifdef DEBUG
    printf("\t\tptr = 0x%p block_size = 0x%x\n", ptr, bt_size(ptr));
    printf("\t\tfirst_block = 0x%p last_block = 0x%p byte_past_heap = 0x%p\n",
           first_block, last_block, byte_past_heap);
#endif
    word_t *bt = ptr;
    // nanana
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
#ifdef DEBUG
      printf("\t\t1\033[3;43;30m[Move to next block]\033[0m next_ptr = 0x%p\n",
             ptr);
#endif
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

#ifdef DEBUG
  printf("\033[3;43;30m[Creating new block]\033[0m at 0x%p ending at 0x%p of "
         "size 0x%x [byte_past_heap]0x%p\n",
         ptr, bt_footer(ptr) + 1, bt_size(ptr), byte_past_heap);
#endif

  return ptr;
}
#else
/* Best fit startegy. */
static word_t *find_fit(size_t reqsz) {
}
#endif

void *malloc(size_t size) {
#ifdef DEBUG
  printf("\033[3;102;30m--== it's malloc time ==--\033[0m\n");
  printf("\033[3;43;30m[mallocing] [reqsz]0x%lx\033[0m\n", size);
  printf("Called mm_checkheap() from malloc\n");
  mm_checkheap(0);
#endif
  size = blksz(size);
#ifdef DEBUG
  printf("[round-up size]0x%lx\n", size);
#endif
  word_t *bt = find_fit(size);
  bt_make(bt, bt_size(bt), USED);
#ifdef DEBUG
  printf("\033[3;102;30m--== mallocked ==-- at 0x%p\033[0m\n\n",
         bt_payload(bt));

  printf("Called mm_checkheap() from malloc\n");
  mm_checkheap(0);
#endif

  return bt_payload(bt);
}

/* --=[ free ]=------------------------------------------------------------- */

void free(void *ptr) {
#ifdef DEBUG
  printf("\033[3;106;30m--== it's freeing time ==--\033[0m\n");
  printf("{free}    [ptr] 0x%p\n", ptr);
#endif
  if (ptr == NULL) {
#ifdef DEBUG
    printf("[ptr=NULL]Haha, very funny.\n");
#endif
    return;
  }

  void *left_block_footer = 0;
#ifdef DEBUG
  size_t left_block_size = 0;
  int left_block_free = -1;
#endif

#ifdef DEBUG
  void *right_block_footer = 0;
  size_t right_block_size = 0;
  int right_block_free = -1;
#endif
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
#ifdef DEBUG
    left_block_size = bt_size(left_block_header);
    left_block_free = bt_free(left_block_header);
#endif
  }
  /* We already can calculate address of the next block's header. */
  void *right_block_header = bt_next(bt);
  if (right_block_header) {
#ifdef DEBUG
    right_block_footer = bt_footer(right_block_header);
    right_block_size = bt_size(right_block_header);
    right_block_free = bt_free(right_block_header);
#endif
  }

  /* Withouth colaescing we don't change current block's bt's. */
  void *new_block_header = bt;
#ifdef DEBUG
  void *new_block_footer = bt_footer(bt);
#endif

  size_t new_block_size = bt_size(bt);

#ifdef DEBUG
  printf("[current block] 0x%p 0x%p 0x%lx [free?] %d\n", new_block_header,
         new_block_footer + sizeof(word_t), new_block_size,
         bt_free(new_block_header));
  printf("[left    block] 0x%p 0x%p 0x%lx [free?] %d\n", left_block_header,
         left_block_footer + sizeof(word_t), left_block_size, left_block_free);
  printf("[right   block] 0x%p 0x%p 0x%lx [free?] %d\n", right_block_header,
         right_block_footer + sizeof(word_t), right_block_size,
         right_block_free);
#endif
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
#ifdef DEBUG
    new_block_footer = right_block_footer;
#endif
    new_block_size += bt_size(right_block_header);
  }
  bt_make(new_block_header, new_block_size, FREE);
#ifdef DEBUG
  printf("[freed   block] 0x%p 0x%p 0x%lx [free?] %d\n", new_block_header,
         new_block_footer + sizeof(word_t), new_block_size,
         bt_free(new_block_header));
#endif
  /* We may connect last block with it's left neighbour, then we have to update
   * last_block pointer. */
  if (bt_next(new_block_header) ==
      NULL) { // maybe this isn't the best way (or even correct way) to do it
    last_block = new_block_header;
  }
#ifdef DEBUG
  printf("\033[3;106;30m--== freed ==--\033[0m\n\n");
  printf("Called mm_checkheap() from free\n");
  mm_checkheap(0);
#endif
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.
 **/
void *realloc(void *old_ptr, size_t size) {
#ifdef DEBUG
  printf("\033[3;46;30m--== it's realloc time ==--\033[0m\n");
  printf("\033[3;46;30m[reallocing][reqsz]0x%lx [round-up size]0x%lx [ptr]0x%p "
         "[bt]0x%p\033[0m \n",
         size, blksz(size), old_ptr, old_ptr - sizeof(word_t));
#endif
  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(size);

  size = blksz(size);

  void *old_bt = old_ptr - sizeof(word_t);
  size_t old_bt_size = bt_size(old_bt);
  void *next_block = bt_next(old_bt);
  // Optimalization 2
  /* If we want to shrink size of the block, we can split it and attach
   * remaining part to the next free block (if it exists). */
  if (old_bt_size > size) {

#ifdef DEBUG
    size_t next_block_size = -1;
    if (next_block)
      next_block_size = bt_size(next_block);
    printf("\033[46;30m[2 OPTIMALIZATION]\033[0m\n");
    printf(
      "[old bt]0x%p [old size]0x%lx [nextblock]0x%p [next size]0x%lx [join]%d "
      "[bt_free(next_block)]%d [old_bt_size > size]%d\n",
      old_bt, old_bt_size, next_block, next_block_size,
      bt_free(next_block) && (old_bt_size > size), bt_free(next_block),
      old_bt_size > size);
#endif

    void *remain_block_bt = old_bt + size;
    size_t remaining_size = bt_size(old_bt) - size;
    bt_make(old_bt, size, USED);

    if (next_block && bt_free(next_block))
      bt_make(remain_block_bt, remaining_size + bt_size(next_block), FREE);
    bt_make(remain_block_bt, remaining_size, FREE);

    if (bt_next(remain_block_bt) ==
        NULL) { // maybe this isn't the best way (or even correct way) to do it
      last_block = remain_block_bt;
    }
  }

  // Optimalization 1
  /* If current block lies next to free block that's large enough, we can join
   * them. */
  if (next_block) {
    size_t next_block_size = bt_size(next_block);
#ifdef DEBUG
    printf("\033[46;30m[1 OPTIMALIZATION]\033[0m\n");
    printf(
      "[old bt]0x%p [old size]0x%lx [nextblock]0x%p [next size]0x%lx [join]%d "
      "[bt_free(next_block)]%d [old_bt_size + next_block_size >= size]%d\n",
      old_bt, old_bt_size, next_block, next_block_size,
      bt_free(next_block) && (old_bt_size + next_block_size >= size),
      bt_free(next_block), old_bt_size + next_block_size >= size);
#endif
    if (bt_free(next_block) && (old_bt_size + next_block_size >= size)) {
      size_t total_size = old_bt_size + next_block_size;
      size_t increased_size = size;
      size_t new_block_size = total_size - size;
      void *new_block = old_bt + increased_size;

#ifdef DEBUG
      printf("[total size]0x%lx [increased size]0x%lx [new block size]0x%lx\n",
             total_size, increased_size, new_block_size);
      printf("[new block]0x%p [new block size]0x%lx [increased size]0x%lx\n",
             new_block, new_block_size, increased_size);
#endif

      bt_make(old_bt, increased_size, USED);
      bt_make(new_block, new_block_size, FREE);

#ifdef DEBUG
      printf("[bt]0x%p [ft]0x%p [size]0x%x [free]%d\n", new_block,
             bt_footer(new_block), bt_size(new_block), bt_free(new_block));
#endif

      if (bt_next(new_block) == NULL) { // maybe this isn't the best way (or
                                        // even correct way) to do it
        last_block = new_block;
#ifdef DEBUG
        printf(
          "[bt]0x%p [ft]0x%p [size]0x%x [free]%d\n[returned payload]0x%p\n",
          new_block, bt_footer(new_block), bt_size(new_block),
          bt_free(new_block), bt_payload(old_bt));
#endif
      }
#ifdef DEBUG
      printf("Called mm_checkheap() from realloc\n");
      mm_checkheap(0);
#endif

      return bt_payload(old_bt);
    }
  }

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
#ifdef DEBUG
  printf("\033[2;103;30m--==::: HEAP :::==--\033[0m\n");
  printf("\033[3;103;30m[first_block] 0x%p  [last_block] 0x%p [byte_past_heap] "
         "0x%p\033[0m\n\n",
         first_block, last_block, byte_past_heap);
#endif

  int block_id = 0;
  void *ptr = first_block;

  /*
   * Traverse heap block by block
   */
  while (ptr) {
#ifdef DEBUG
    printf("[id]%d  [hd]0x%p  [ft]0x%p  [free]%d  [size]0x%x\n", block_id, ptr,
           bt_footer(ptr), bt_free(ptr), bt_size(ptr));
#endif
    // ptr = bt_next(ptr);

    word_t *next = ptr + bt_size(ptr);

    if (next > (word_t *)last_block || next == ptr) {
#ifdef DEBUG
      printf("\t[next > last_block]0x%p > 0x%p [next == ptr]0x%p == 0x%p\n",
             next, last_block, next, ptr);
#endif
      next = NULL;
    }

    if (first_block > last_block) {
#ifdef DEBUG
      printf("\033[2;101;30m<ERROR>\033[0m [first_block > last_block]%d "
             "[first_block]0x%p [last_block]0x%p\n",
             first_block > last_block, first_block, last_block);
#endif
      exit(1);
    }

    if (last_block > byte_past_heap) {
#ifdef DEBUG
      printf("\033[2;101;30m<ERROR>\033[0m [last_block > byte_past_heap]%d "
             "[last_block]0x%p [byte_past_heap]0x%p\n",
             last_block > byte_past_heap, last_block, byte_past_heap);
#endif
      exit(1);
    }

    ptr = next;
    block_id++;
  }

#ifdef DEBUG
  printf("\033[2;103;30m[--==::: HEAPPY END :::==--\033[0m\n\n");
#endif
}
