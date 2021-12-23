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

/*
  Imię: Krystian
  Nazwisko: Jasionek
  Nr indeksu: 317806

  Oświadczam, że poniższe rozwiązanie zostało wykonane przeze mnie samodzielnie.
*/

/* If you want debugging output, use the following macro.
 * When you hand in, remove the #define DEBUG line. */
#define FREELISTDEBUG
// #define DEBUG
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
  FREE = 0b000,     /* Block is free */
  USED = 0b001,     /* Block is used */
  PREVFREE = 0b010, /* Previous block is free (optimized boundary tags) */
} bt_flags;

static void *first_block;    /* Address of the first block */
static void *byte_past_heap; /* Address past last byte of last block */
static void *last_block;     /* Points at last block */

static void *root;
static word_t root_next_offset;
static word_t root_prev_offset;

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
  printf("\t\t\t\033[3;42;30m{bt_next}\033[0m bt = %p move by 0x%x\n", bt,
         bt_size(bt));
#endif
  word_t *next = bt + bt_size(bt) / sizeof(word_t);

  // if (next > (word_t *)last_block || next == bt) {
  if (bt == (word_t *)last_block) {
#ifdef DEBUG
    printf(
      "\033[3;101;30mbt_next() returned NULL [next]%p [last_block]%p\033[0m\n",
      next, last_block);
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
  printf("\t\t\t\033[3;42;30m{bt_prev}\033[0m [bt] %p [shift] 0x%x [prevft] "
         "%p [prevbt] %p\n",
         bt, bt_size(prev_footer), prev_footer, prev);
#endif
  if (bt == first_block)
    return NULL;

  return prev;
}

/* --=[ free blocks list handling
 * ]=----------------------------------------------------------- */

/* Returns pointer to the beginning of the block that lies 'offset' bytes from
 * the heap start. */
static inline void *get_block_ptr(word_t offset) {
  return mem_heap_lo() + offset;
}

/* Calculates offset from heap start to the start of the block based on pointer
 * to the block start. */
static inline word_t get_offset(void *ptr) {
  return (uint64_t)ptr & 0x00000000FFFFFFFF;
}

/* Sets block's offset to the next free block on the list. */
static inline void set_free_block_next(word_t *block_bt, word_t *next) {
  *(block_bt + 1) = get_offset(next);
#ifdef DEBUG
  printf("[set next] [bt]%p [next_off]0x%x [next]0x%x\n", block_bt,
         get_offset(next), *(block_bt + 1));
#endif
}

/* Sets block's offset to the previous free block on the list. */
static inline void set_free_block_prev(word_t *block_bt, word_t *prev) {
  *(block_bt + 2) = get_offset(prev);
}

/* Sets offsets to the next and previous free blocks on the list. */
static inline void set_free_block_offsets(word_t *block_bt, word_t *next,
                                          word_t *prev) {
  set_free_block_next(block_bt, next);
  set_free_block_prev(block_bt, prev);
}

/* Returns block's offset to the next free block on the list. */
static inline word_t get_free_block_next_off(word_t *block_bt) {
  return *(block_bt + 1);
}

/* Returns pointer to the next free block on the list. */
static inline void *get_free_block_next_ptr(word_t *block_bt) {
  return get_block_ptr(get_free_block_next_off(block_bt));
}

/* Returns block's offset to the previous free block on the list. */
static inline word_t get_free_block_prev_off(word_t *block_bt) {
  return *(block_bt + 2);
}

/* Returns pointer to the previous free block on the list. */
static inline void *get_free_block_prev_ptr(word_t *block_bt) {
  return get_block_ptr(get_free_block_prev_off(block_bt));
}

/* Iterates over blocks on the free blocks list. */
static inline void traverse_free_block_list() {
#ifdef DEBUG
  printf("\033[3;30;47;30m--==::: Free Blocks List :::==--\n");
  int id = 0;
#endif
  void *current =
    mem_heap_lo() + root_next_offset; // address of first free block
#ifdef DEBUG
  printf("\033[3;30;47;30m[current]%p [heap_lo]%p [root]%p "
         "[root_next_offset]0x%x [root_prev_offset]0x%x\n",
         current, mem_heap_lo(), root, root_next_offset, root_prev_offset);
#endif
  while (current != root) {
#ifdef DEBUG
    printf("\033[3;30;47;30m[id]%d [bt]0x%p [next_off]0x%x [next]%p "
           "[prev_off]0x%x [prev]%p\n"
           "\033[3;30;47;30m\t[bt]%p [ft]%p [size]0x%x\n",
           ++id, current, get_free_block_next_off(current),
           get_free_block_next_ptr(current), get_free_block_prev_off(current),
           get_free_block_prev_ptr(current), current, bt_footer(current),
           bt_size(current));
#endif
    current = get_free_block_next_ptr(current);
  }
#ifdef DEBUG
  printf("\033[3;30;47;30m--==::: List End :::==--\033[0m\n");
#endif
}

/* Adds new free block on the list and set's it's offsets to the next and
 * previous free blocks on the list. */
static inline void free_list_push_front(void *ptr) {
#ifdef DEBUG
  printf("\033[3;30;47;30m--==::: List Push Front :::==--\n");
#endif
  void *curr_first_block = get_block_ptr(root_next_offset);

  root_next_offset = get_offset(ptr);
  if (root_prev_offset == 0) // It's first free block in a list
    root_prev_offset = root_next_offset;
  else
    set_free_block_prev(curr_first_block, ptr);

  set_free_block_offsets(ptr, curr_first_block, root);

#ifdef DEBUG
  printf("\033[3;30;47;30m[ptr]%p [next_off]0x%x [next]%p [prev_off]0x%x "
         "[prev]%p [root_next_off]0x%x [root_prev_off]0x%x [curr_first]%p\n",
         ptr, get_free_block_next_off(ptr), get_free_block_next_ptr(ptr),
         get_free_block_prev_off(ptr), get_free_block_prev_ptr(ptr),
         root_next_offset, root_prev_offset, curr_first_block);
  printf("\033[3;30;47;30m--==::: Push End :::==--\033[0m\n");
  traverse_free_block_list();
#endif
}

/* Removes block starting at address `ptr` from free blocks list and changes
 * it's neigbhours offsets. */
static inline void free_list_remove(void *ptr) {
#ifdef DEBUG
  printf("\033[3;30;47;30m--==::: List Remove :::==--\n");
#endif
  void *prev_bt = get_free_block_prev_ptr(ptr);
  void *next_bt = get_free_block_next_ptr(ptr);
#ifdef DEBUG
  printf("\033[3;30;47;30m[ptr]%p [prev_bt]%p [next_bt]%p\n", ptr, prev_bt,
         next_bt);
#endif
  if (prev_bt ==
      next_bt) { // only one block in list (prev_bt == next_bt == root)
#ifdef DEBUG
    printf("\033[3;30;47;30m[first block] [root]%p [root_prev]0x%x "
           "[root_next]0x%x\n",
           root, root_prev_offset, root_next_offset);
#endif
    root_prev_offset = 0;
    root_next_offset = 0;
  } else if (next_bt == root) {
#ifdef DEBUG
    printf("\033[3;30;47;30m[next==root] [root]%p [root_prev]0x%x "
           "[root_next]0x%x [prev_bt]%p\n",
           root, root_prev_offset, root_next_offset, prev_bt);
#endif
    set_free_block_next(prev_bt, root);
    root_prev_offset = get_offset(prev_bt);
  } else if (prev_bt == root) {
#ifdef DEBUG
    printf("\033[3;30;47;30m[prev==root] [root]%p [root_prev]0x%x "
           "[root_next]0x%x [next_bt]%p\n",
           root, root_prev_offset, root_next_offset, next_bt);
#endif
    set_free_block_prev(next_bt, root);
    root_next_offset = get_offset(next_bt);
  } else {
#ifdef DEBUG
    printf("\033[3;30;47;30m[normal case] [root]%p [root_prev]0x%x "
           "[root_next]0x%x [next_bt]%p [prev_bt]%p\n",
           root, root_prev_offset, root_next_offset, next_bt, prev_bt);
#endif
    set_free_block_prev(next_bt, prev_bt);
    set_free_block_next(prev_bt, next_bt);
  }

#ifdef DEBUG
  printf("\033[3;30;47;30m--==::: Remove End :::==--\033[0m\n");
  traverse_free_block_list();
#endif
}

/* --=[ miscellanous procedures ]=------------------------------------------ */

/* Rounds up given size to match the alignment. */
static inline size_t round_up(size_t size) {
  return (size + ALIGNMENT - 1) & -ALIGNMENT;
}

/* Calculates block size incl. header, footer & payload,
 * and aligns it to block boundary (ALIGNMENT). */
static inline size_t blksz(size_t size) {
  return round_up(size + 2 * sizeof(word_t));
}

/* Divides block starting at `bt` into two blocks. */
static inline void split(word_t *bt, size_t size) {
  word_t *remain_block_bt = bt + size / sizeof(word_t);
  size_t remaining_size = bt_size(bt) - size;

  /* We may split last block, then we have to update last_block pointer. */
  if (bt == last_block) { // maybe this isn't the best way (or even correct way)
                          // to do it
    last_block = remain_block_bt;
  }

  /* Create two new blocks. */
  bt_make(bt, size, FREE);
  bt_make(remain_block_bt, remaining_size, FREE);

#ifdef DEBUG
  printf("\t\033[3;42;30m{split}\033[0m\033[3;45;30m[splitting block]\033[0m "
         "[left]%p:%p (size)0x%x [right]%p:%p (size)0x%x (rmsz)0x%lx\n",
         bt, bt_footer(bt), bt_size(bt), remain_block_bt,
         bt_footer(remain_block_bt), bt_size(remain_block_bt), remaining_size);
#endif

#ifdef FREELISTDEBUG
  /* Add newly created free block to the free block list, remove old and update
   * it's successor's offset to previous block. */
  free_list_remove(bt);
  free_list_push_front(remain_block_bt);
  // set_free_block_next(get_free_block_prev_ptr(bt), remain_block_bt);
#endif
}

/* --=[ mm_init ]=---------------------------------------------------------- */

/* Intializes global variables and heap. */
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

  root = mem_heap_lo();
  root_next_offset = 0;
  root_prev_offset = 0;

#ifdef DEBUG
  printf("%p %p %p %p\n\033[3;46;30m--== initialized ==--\033[0m\n", ptr,
         first_block, last_block, byte_past_heap);
#endif

  return 0;
}

/* --=[ malloc ]=----------------------------------------------------------- */

static word_t *find_free_block(size_t reqsz) {
#ifdef DEBUG
  printf("\033[3;30;47;30m--==::: Finding Free Block :::==--\n");
  int id = 0;
#endif
  void *current =
    mem_heap_lo() + root_next_offset; // address of first free block
#ifdef DEBUG
  printf(
    "\033[3;30;47;30m[current]%p [heap_lo]%p [root_next_offset]0x%x [root]%p\n",
    current, mem_heap_lo(), root_next_offset, root);
#endif
  while (current != root) {
#ifdef DEBUG
    printf("\033[3;30;47;30m[id]%d [bt]0x%p [next_off]0x%x [next]%p "
           "[prev_off]0x%x [prev]%p\n",
           ++id, current, get_free_block_next_off(current),
           get_free_block_next_ptr(current), get_free_block_prev_off(current),
           get_free_block_prev_ptr(current));
#endif
    size_t current_block_size = bt_size(current);
    if (current_block_size == reqsz) {
      free_list_remove(current);
      return current;
    }
    if (current_block_size > reqsz) {
      split(current, reqsz);
      return current;
    }

    current = get_free_block_next_ptr(current);
  }
#ifdef DEBUG
  printf("\033[3;30;47;30m--==::: List End :::==--\033[0m\n");
#endif
  // void *ptr = mem_sbrk(reqsz);
  // bt_make(ptr, reqsz, USED);
  // last_block = ptr;
  // byte_past_heap = ptr + reqsz;

#ifdef DEBUG
  printf("\033[3;43;30m[Creating new block]\033[0m at %p ending at %p of "
         "size 0x%x [byte_past_heap]%p\n",
         ptr, bt_footer(ptr) + 1, bt_size(ptr), byte_past_heap);
#endif

  // return ptr;
  return NULL;
}

#if 1
#ifndef FREELISTDEBUG
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
    printf("\t\tptr = %p block_size = 0x%x\n", ptr, bt_size(ptr));
    printf("\t\tfirst_block = %p last_block = %p byte_past_heap = %p\n",
           first_block, last_block, byte_past_heap);
#endif
    word_t *bt = ptr;
    /*
     * Current block is exactly the same size as reqiested and free, so we can
     * simply return it.
     */
    if ((bt_size(ptr) == reqsz) && bt_free(ptr)) {
#ifdef FREELISTDEBUG
      free_list_remove(ptr);
#endif
      return bt;
    }
    /*
     * Current block is larger than requested size, so we split it into two
     * block -- of `reqsz` bytes and of remaining bytes.
     */
    else if ((bt_size(ptr) > reqsz) && bt_free(ptr)) {
      split(ptr, reqsz);

#ifdef FREELISTDEBUG
      void *new_free_block = bt_next(ptr);
      free_list_remove(ptr);
      free_list_push_front(new_free_block);
#endif

      return ptr;
    }
    /*
     * Current block is too small or used, so we move to the next one.
     */
    else {
      ptr = bt_next(ptr);
#ifdef DEBUG
      printf("\t\t1\033[3;43;30m[Move to next block]\033[0m next_ptr = %p\n",
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
  printf("\033[3;43;30m[Creating new block]\033[0m at %p ending at %p of "
         "size 0x%x [byte_past_heap]%p\n",
         ptr, bt_footer(ptr) + 1, bt_size(ptr), byte_past_heap);
#endif

  return ptr;
}
#endif
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
#ifdef FREELISTDEBUG
  word_t *bt = find_free_block(size);

  if (bt == NULL){
    bt = mem_sbrk(size);
    // bt_make(bt, size, USED);
    last_block = bt;
    byte_past_heap = bt + size;
  }
#ifdef DEBUG
  printf("Free list found: [bt]%p [ft]%p [size]0x%x\n", bt, bt_footer(bt),
         bt_size(bt));
#endif
#endif
  // bt_make(bt, bt_size(bt), USED);
  bt_make(bt, size, USED);
#ifdef DEBUG
  printf("\033[3;102;30m--== mallocked ==-- at %p\033[0m\n\n", bt_payload(bt));

  printf("Called mm_checkheap() from malloc\n");
  mm_checkheap(0);
#endif

  return bt_payload(bt);
}

/* --=[ free ]=------------------------------------------------------------- */

void free(void *ptr) {
#ifdef DEBUG
  printf("\033[3;106;30m--== it's freeing time ==--\033[0m\n");
  printf("{free}    [ptr] %p\n", ptr);
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

  printf("[left    block] %p %p 0x%lx [free?] %d\n", left_block_header,
         left_block_footer + sizeof(word_t), left_block_size, left_block_free);
  printf("[current block] %p %p 0x%lx [free?] %d\n", new_block_header,
         new_block_footer + sizeof(word_t), new_block_size,
         bt_free(new_block_header));
  printf("[right   block] %p %p 0x%lx [free?] %d\n", right_block_header,
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
#ifdef FREELISTDEBUG
    free_list_remove(left_block_header);
#endif
  }

  /* We shift new_block_footer to the right if right neighbour is free and is
   * inside the heap. */
  int coalesced_right = 0;
  if (right_block_header && bt_free(right_block_header)) {
#ifdef DEBUG
    new_block_footer = right_block_footer;
#endif
    new_block_size += bt_size(right_block_header);
    coalesced_right = 1;
#ifdef FREELISTDEBUG
    free_list_remove(right_block_header);
#endif
  }
  bt_make(new_block_header, new_block_size, FREE);
#ifdef DEBUG
  printf("\n[freed   block] %p %p 0x%lx [free?] %d\n", new_block_header,
         new_block_footer + sizeof(word_t), new_block_size,
         bt_free(new_block_header));
#endif
  /* We may connect last block with it's left neighbour, then we have to update
   * last_block pointer. */
  if ((bt == last_block) ||
      ((right_block_header == last_block) &&
       coalesced_right)) { // maybe this isn't the best way (or even correct
                           // way) to do it
    last_block = new_block_header;
  }
#ifdef FREELISTDEBUG
  free_list_push_front(new_block_header);
#endif

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
  printf("\033[3;46;30m[reallocing][reqsz]0x%lx [round-up size]0x%lx [ptr]%p "
         "[bt]%p\033[0m \n",
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

  // Optimalization 3
  /* We want to increase size by a insignificant ammount, but our block may
   * already have padding, so we don't have to do anything. */
  // printf("0x%lx == 0x%lx => %d \n", size, old_bt_size, size == old_bt_size);
  if (size == old_bt_size) {
#ifdef DEBUG
    printf("\033[46;30m[3 OPTIMALIZATION -- Already good address]\033[0m\n");
    printf("[size]0x%lx [old bt size]0x%lx\n", size, old_bt_size);
#endif
    return old_ptr;
  }

  // Optimalization 2
  /* If we want to shrink size of the block, we can split it and attach
   * remaining part to the next free block (if it exists). */
  if (old_bt_size > size) {
#ifdef DEBUG
    size_t next_block_size = -1;
    if (next_block)
      next_block_size = bt_size(next_block);
    printf("\033[46;30m[2 OPTIMALIZATION -- Shrinking block (and joining new "
           "free block with next free block)]\033[0m\n");
    printf("[old bt]%p [old size]0x%lx [nextblock]%p [next size]0x%lx [join]%d "
           "[bt_free(next_block)]%d [old_bt_size > size]%d\n",
           old_bt, old_bt_size, next_block, next_block ? next_block_size : 0,
           next_block ? bt_free(next_block) && (old_bt_size > size) : -1,
           next_block ? bt_free(next_block) : -1, old_bt_size > size);
#endif

    void *remain_block_bt = old_bt + size;
    size_t remaining_size = old_bt_size - size;
    bt_make(old_bt, size, USED);

    /* If next block is free we can coalesce the rest of current block with it.
     */
    if (next_block && bt_free(next_block)) {
      bt_make(remain_block_bt, remaining_size + bt_size(next_block), FREE);
#ifdef FREELISTDEBUG
      free_list_remove(next_block);
      free_list_push_front(remain_block_bt);
#ifdef DEBUG
      printf("[free list coallescing] [old]%p [old_prev]%p [old_next]%p "
             "[new]%p [next_prev]%p [next_next]%p\n",
             next_block, get_free_block_prev_ptr(next_block),
             get_free_block_next_ptr(next_block), remain_block_bt,
             get_free_block_prev_ptr(remain_block_bt),
             get_free_block_next_ptr(remain_block_bt));
#endif
#endif
    } else {
      bt_make(remain_block_bt, remaining_size, FREE);
#ifdef FREELISTDEBUG
      free_list_push_front(remain_block_bt);
#ifdef DEBUG
      printf("[free list add remain] [remain_bt]%p [remain_bt_prev]%p "
             "[remain_bt_next]%p\n",
             remain_block_bt, get_free_block_prev_ptr(remain_block_bt),
             get_free_block_next_ptr(remain_block_bt));
#endif
#endif
    }

    if (old_bt == last_block) { // maybe this isn't the best way (or even
                                // correct way) to do it
      last_block = remain_block_bt;
    }

    return old_ptr;
  }

  // Optimalization 4
  /* If we're trying to realloc the last block, we can simply increase heap
  size. */
  if (old_bt == last_block && (size > old_bt_size)) {
    size_t increase_size = size - old_bt_size;
    void *ptr = mem_sbrk(increase_size);

    bt_make(old_bt, size, USED);
    last_block = old_bt;
    byte_past_heap = ptr + increase_size;

#ifdef DEBUG
    printf("\033[46;30m[4 OPTIMALIZATION -- Increase heap size]\033[0m\n");
    printf("[size]0x%lx [old bt size]0x%lx [increase size]0x%lx [bt]%p [last "
           "block]%p [byte past heap]%p\n",
           size, old_bt_size, increase_size, old_bt, last_block,
           byte_past_heap);
#endif

    return bt_payload(old_bt);
  }

  // Optimalization 1
  /* If current block lies next to free block that's large enough, we can join
   * them. */
  if (next_block) {
    size_t next_block_size = bt_size(next_block);
#ifdef DEBUG
    printf("\033[46;30m[1 OPTIMALIZATION -- Expanding block and joining with "
           "right neighbour]\033[0m\n");
    printf(
      "[old bt]%p [old size]0x%lx [nextblock]%p [next size]0x%lx [join]%d "
      "[bt_free(next_block)]%d [old_bt_size + next_block_size >= size]%d\n",
      old_bt, old_bt_size, next_block, next_block_size,
      bt_free(next_block) && (old_bt_size + next_block_size >= size),
      bt_free(next_block), old_bt_size + next_block_size >= size);
#endif
    /* We will join neighbouring free blocks. */
    if (bt_free(next_block) && (old_bt_size + next_block_size >= size)) {
      size_t total_size = old_bt_size + next_block_size;
      size_t increased_size = size;
      size_t new_block_size = total_size - size;
      void *new_block = old_bt + increased_size;

#ifdef DEBUG
      printf("[total size]0x%lx [increased size]0x%lx [new block size]0x%lx\n",
             total_size, increased_size, new_block_size);
      printf("[new block]%p [new block size]0x%lx [increased size]0x%lx\n",
             new_block, new_block_size, increased_size);
#endif

      bt_make(old_bt, increased_size, USED);
#ifdef FREELISTDEBUG
      free_list_remove(next_block);
#endif
      if (new_block_size > 0) {
        bt_make(new_block, new_block_size, FREE);
#ifdef FREELISTDEBUG
        free_list_push_front(new_block);
#endif
      }

#ifdef DEBUG
      printf("[bt]%p [ft]%p [size]0x%x [free]%d\n", new_block,
             bt_footer(new_block), bt_size(new_block), bt_free(new_block));
#endif

      if (next_block == last_block) { // maybe this isn't the best way (or
                                      // even correct way) to do it
        if (new_block_size > 0)
          last_block = new_block;
        else
          last_block = old_bt;
#ifdef DEBUG
        printf("[last_block=new_block][bt]%p [ft]%p [size]0x%x "
               "[free]%d\n[returned payload]%p\n",
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
  printf("\033[3;103;30m[first_block] %p  [last_block] %p [byte_past_heap] "
         "%p\033[0m\n\n",
         first_block, last_block, byte_past_heap);
#endif

  int block_id = 0;
  void *ptr = first_block;

  /*
   * Traverse heap block by block
   */
  while (ptr) {
#ifdef DEBUG
    printf("[id]%d  [hd]%p  [ft]%p  [free]%d  [size]0x%x\n", block_id, ptr,
           bt_footer(ptr), bt_free(ptr), bt_size(ptr));
#endif
    // ptr = bt_next(ptr);

    word_t *next = ptr + bt_size(ptr);

    if (next > (word_t *)last_block || next == ptr) {
#ifdef DEBUG
      printf("\t[next > last_block]%p > %p [next == ptr]%p == %p\n", next,
             last_block, next, ptr);
#endif
      next = NULL;
    }

    if (first_block > last_block) {
#ifdef DEBUG
      printf("\033[2;101;30m<ERROR>\033[0m [first_block > last_block]%d "
             "[first_block]%p [last_block]%p\n",
             first_block > last_block, first_block, last_block);
#endif
      exit(1);
    }

    if (last_block > byte_past_heap) {
#ifdef DEBUG
      printf("\033[2;101;30m<ERROR>\033[0m [last_block > byte_past_heap]%d "
             "[last_block]%p [byte_past_heap]%p\n",
             last_block > byte_past_heap, last_block, byte_past_heap);
#endif
      exit(1);
    }

    if (next && bt_free(ptr) && bt_free(next)) {
#ifdef DEBUG
      printf("\033[2;101;30m<ERROR>\033[0m [free neighbours]%d "
             "[current blok]%p [next block]%p\n",
             bt_free(ptr) && bt_free(next), ptr, next);
#endif
      exit(1);
    }

    ptr = next;
    block_id++;
  }

#ifdef FREELISTDEBUG
  traverse_free_block_list();
#endif
#ifdef DEBUG
  printf("\033[2;103;30m[--==::: HEAPPY END :::==--\033[0m\n\n");
#endif
}
