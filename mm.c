/*
 * mm.c -
 * Explicit free list implementation using a LIFO algorithm
 *
 * Name: Aditya Aiyer
 * Andrew ID: aaiyer
 *
 * METHOD:
 * Used an explicit free list that uses a modification of both
 * the best fit and first fit searching algorithms. Used LIFO
 * when inserting free blocks into the free list.
 *
 * MM_INIT:
 * This function initializes the heap with padding, a header, 2 pointers
 * prev and next, a footer and an epilogue block. The heap is then extended
 * by CHUNKSIZE bytes. I deduced an optimum CHUNKSIZE through trial and error.
 * The function returns 0 on success and -1 in case of an error(out of memory
 * perhaps).
 *
 * MM_MALLOC:
 * This function allocates a part of memory that is at least size bytes.
 * Alignment is performed in this function to round the requested bytes
 * to the nearest multiple of ALIGNMENT and then DSIZE bytes is added to
 * accomodate for the header and footer. The header and footer contain the
 * sizes and allocated bit. The allocated bit is set to 1 when malloc is called.
 * findFit is used to find a good fit in the free block list for the requested
 * bytes of memory. The free block is then changed into an allocated one in the
 * place function.
 *
 * MM_FREE:
 * This function deallocates an allocated portion of memory. It sets
 * the allocated bit to zero.
 * Newly freed blocks are placed at the beginning of the free list
 * as per LIFO.
 * It is possible that free block(s) lie next to a newly freed block.
 * In such a case, we coalesce the free blocks.
 *
 * MM_REALLOC:
 * This function is similar to malloc except for the fact that we may shrink
 * the block pointer to by ptr(argument of realloc).
 * If the size is the same, we just return the pointer. If the new size is less
 * then we copy the number of new size bytes to another location and free
 * the old block.
 *
 * CALLOCING:
 * This is essentially mallocing the data and then initializing the data to
 * zero.
 *
 * CHECKHEAP:
 * This is a function taht runs silently and prints an error message if one of
 * the heap invariants is not satisfied.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
# define dbg_mm_checkheap(...) mm_checkheap(__VA_ARGS__)
#else
# define dbg_printf(...)
# define dbg_mm_checkheap(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* Double word (8) alignment */
#define ALIGNMENT 8

/* Constant for findFit function */
#define CONSTANT 14

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* Basic constants and macros */
#define WSIZE           4        /* word size (bytes) */
#define DSIZE           8        /* doubleword size (bytes) */
#define CHUNKSIZE       300      /* initial heap size (bytes) */
#define MINBLOCKSIZE    24       /* minimum block size */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(int *)(p))
#define PUT(p, val)  (*(int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((void *)(bp) - WSIZE)
#define FTRP(bp)       ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((void *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp)  ((void *)(bp) - GET_SIZE(HDRP(bp) - WSIZE))

/* Given block ptr bp, compute address of next and previous free blocks */
#define PREV_FREE(bp)  (*(void **)(bp))
#define NEXT_FREE(bp)  (*(void **)(bp + DSIZE))

/* Global variables */
static char *heap_listp = 0; /* Pointer to the first block */
static char *free_listp;     /* Pointer to the first free block */

/* Function prototypes for internal helper routines */
static void *extendHeap(size_t words);
static void place(void *bp, size_t asize);
static void *findFit(size_t asize);
static void *coalesce(void *bp);
static void insertAtFront(void *bp);
static void delBlkFromFreeList(void *bp);
static void checkblock(void *bp);
static void printblock(void *bp);
static void checkFreeNodes(void *bp);
static void checkInFreeList(void *bp);

/*
 * mm_init - Heap initializer
 *
 * mm_init initializes the heap by first creating an
`* initial block described in the function and then
 * extending the heap by chunksize/dsize. The initial heap
 * consists of a single free block. The minimum block size
 * is 24 bytes because we require 8 for both the header and
 * and footer and 8 each for the next and prev pointers of
 * the doubly linked list.
 */
int mm_init(void)
{
  /* Initial Block has
   * PADDING|HEADER | PREV PTR | NEXT PTR | FOOTER | EPILOGUE BLOCK|
   * 4 BYTES|4 BYTES| 8 BYTES  |  8 BYTES   |  4 BYTES |    4 BYTES    |
   * for a total of MINBLOCKSIZE+DSIZE  */

  /*return -1 if unable to get heap space*/
  if ((heap_listp = mem_sbrk(DSIZE+MINBLOCKSIZE)) == NULL)
    return -1;

  PUT(heap_listp, 0); /* Alignment padding */

  /*Initialize prologue block header and footer
   * and pointers.
   * 4 bytes for header
   * 4 bytes for footer
   * 8 bytes for prev ptr,
   * 8 bytes for next ptr */
  PUT(heap_listp + WSIZE, PACK(MINBLOCKSIZE, 1)); //HEADER
  PUT(heap_listp + DSIZE, 0); //PREV ptr
  PUT(heap_listp + 2*DSIZE, 0); //NEXT ptr
  PUT(heap_listp + MINBLOCKSIZE, PACK(MINBLOCKSIZE, 1)); // FOOTER


  PUT(heap_listp+ MINBLOCKSIZE + WSIZE, PACK(0, 1)); // Epilogue Block

  /* Set free list pointer to point to first word of
   * payload in the first free block. */
  free_listp = heap_listp + DSIZE;

  /* Set heap pointer to point to first word AFTER header */
  heap_listp += DSIZE;
  //mm_checkheap(0);

  if (extendHeap(CHUNKSIZE/DSIZE) == NULL)
    return -1;
  //mm_checkheap(0);
  return 0;
}

/*
 * mm_malloc - The allocator
 * malloc allocates free blocks on the heap.
 * It first aligns the size by rounding size to
 * the nearest multiple of ALIGNMENT(8) and then
 * adds DSIZE to this value to accomodate the header
 * and footer. We then call findFit to find a free block
 * that can accomodate this size. After doing so, we
 * set the allocated bit in the header and return the
 * current block pointer.
 */
void *mm_malloc(size_t size)
{

  size_t asize;      /* adjusted block size */
  size_t extendsize; /* amount to extend heap if no fit */
  char *bp;          /* Block pointer to be returned. */

  /* Ignore spurious requests */
  if (size <= 0)
    return NULL;

  /* Adjust block size to include overhead(by adding DSIZE) for header+footer
   *  and alignment reqs */
  asize = MAX(ALIGN(size) + DSIZE, MINBLOCKSIZE);

  /* Search the free list for a fit */
  if ((bp = findFit(asize)) != NULL)
    {
      place(bp, asize);
      //mm_checkheap(0);
      return bp;
    }

  /* No fit found. Get more memory and place the block */
  extendsize = MAX(asize, CHUNKSIZE);

  /* Return NULL if unable to get heap space */
  if ((bp = extendHeap(extendsize/WSIZE)) == NULL)
    return NULL;

  place(bp, asize);
  //mm_checkheap(0);
  return bp;
}

/*
 * mm_free - Freeing memory from the heap.
 * mm_free frees the block pointer to by bp.
 * This function sets the allocated bit of the
 * block pointed to by bp to zero and then coalesces
 * the newly freed block.
 */
void mm_free(void *bp)
{
  if(bp == NULL)
    return;
  size_t size = GET_SIZE(HDRP(bp));

  /* Set header and footer to unallocated */
  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));

  /* Coalesce and need to add the block to the free list */
  coalesce(bp);
  //mm_checkheap(0);
}

/*
 * coalesce
 * Coalesce combines multiple free blocks into one single
 * free block using boundary tag coalescing. This prevents internal
 * fragmentation and also increases throughput since we do not have
 * to traverse multiple blocks.
 *
 * We take 4 cases.
 * Case 1: Previous AND next blocks allocated. Just return pointer.
 * Case 2: Previous free, Next allocated.
 * Case 3: Next free, Previous allocated.
 * Case 4: Previous and next free.
 *
 * The main part of the function first sets up the free block for
 * insertion into the free list. Once it is ready, we insert the free list
 * using a LIFO algorithm.
 */
static void *coalesce(void *bp)
{
  size_t prev_alloc = PREV_BLKP(bp) == bp || GET_ALLOC(HDRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size;

  /* Case 1 */
  if(prev_alloc && next_alloc)
    {
      /* Insert new free block at front of free list. (LIFO) */
      insertAtFront(bp);
      return bp;
    }

  size = GET_SIZE(HDRP(bp));

  /* Case 2 */
  if (!prev_alloc && next_alloc)
    {
      /* Go to previous block and set size to
       * sum of sizes of current block and
       * previous block. Remove the block from
       * the free list and reset allocated bit.
       */
      bp = PREV_BLKP(bp);
      size += GET_SIZE(HDRP(bp));
      delBlkFromFreeList(bp);
      PUT(HDRP(bp), PACK(size, 0));
      PUT(FTRP(bp), PACK(size, 0));
    }

  /* Case 3 */
  if (prev_alloc && !next_alloc)
    {
      /* Get size.
       * Remove the next block from the free list
       * ready the free block.
       */
      size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
      delBlkFromFreeList(NEXT_BLKP(bp));
      PUT(HDRP(bp), PACK(size, 0));
      PUT(FTRP(bp), PACK(size, 0));
    }

  /* Case 4 */
  else if (!prev_alloc && !next_alloc)
    {
      /* We get the size and remove the next and previous
       * blocks from the free list. We then move the block
       * pointer to the previous block and ready the block
       * for insertion into the free list.
       */
      size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
	GET_SIZE(HDRP(NEXT_BLKP(bp)));
      delBlkFromFreeList(PREV_BLKP(bp));
      delBlkFromFreeList(NEXT_BLKP(bp));
      bp = PREV_BLKP(bp);
      PUT(HDRP(bp), PACK(size, 0));
      PUT(FTRP(bp), PACK(size, 0));
    }

  /* Insert the block pointer to by bp at the front of the free list. */
  insertAtFront(bp);

  return bp;
}


/*
 * mm_realloc. - Reallocates memory
 * Returns a pointer to an allocated region of at least size bytes
 * If ptr is NULL, the call is equivalent to malloc(size);
 * If size is equal to zero, the call is equivalent to free(ptr).
 * The call to realloc takes an existing block of memory, pointed to
 * by ptr and then allocates a region of memory large enough to hold
 * size bytes and returns the address of this new block.
 * The contents of the new block are the same as those of the old ptr
 * block, up to the minimum of  the old and new sizes.
 */
void *mm_realloc(void *ptr, size_t size)
{
  size_t oldsize;
  void *newptr;
  size_t asize;
  /* If size <= 0 then this is just free, and we return NULL. */
  if(size <= 0)
    {
      mm_free(ptr);
      return NULL;
    }

  /* If oldptr is NULL, then this is just malloc. */
  if(ptr == NULL)
    return mm_malloc(size);

  /* Compute size taking into account overhead and alignment */
  asize = MAX(ALIGN(size) + DSIZE,MINBLOCKSIZE);

  /* Get the size of the original block */
  oldsize = GET_SIZE(HDRP(ptr));

  /* We can leave the block and heap as they are. */
  if (asize == oldsize)
    return ptr;

  newptr = mm_malloc(size);

  /* If realloc() fails the original block is left untouched  */
  if(!newptr) {
    return NULL;
  }

  /* Copy the old data. */
  if(asize < oldsize) oldsize = size;
  memcpy(newptr, ptr, oldsize);

  /* Free the old block. */
  mm_free(ptr);
  //mm_checkheap(0);
  return newptr;
}

/*
 * calloc - Allocates memory and initializes it as well.
 * We call malloc on the total number of bytes and then
 * initialize everything to the "zero value" of that type.
 */
void *calloc (size_t nmemb, size_t size)
{
  /* Total bytes */
  size_t bytes = nmemb * size;
  void *newptr;

  newptr = malloc(bytes);

  /* Initialize block pointed to by newptr */
  memset(newptr, 0, bytes);

  return newptr;
}

/*
 * mm_checkheap - Checks the invariants of the heap
 * This function checks the invariants of the heap such as header-footer match,
 * absence of contiguous blocks of free memory and confirmation that the
 * block pointers are within the heaps boundaries.
 */
void mm_checkheap(int verbose)
{
  void *bp = heap_listp; //Points to the first block in the heap
  verbose = verbose;

  /* If first block's header's size or allocation bit is wrong,
   * the prologue header is incorrect. */

  if ((GET_SIZE(HDRP(heap_listp)) != MINBLOCKSIZE) ||
      !GET_ALLOC(HDRP(heap_listp)))
    printf("Bad prologue header\n");
  checkblock(bp);

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
      if (verbose)
	printblock(bp);
      if(GET_SIZE(HDRP(bp)) == 0)
	printf("Error: block has zero size\n");
      checkblock(bp);

      /* Checking to see if free block in the free list */
      if(!GET_ALLOC(HDRP(bp)))
	checkInFreeList(bp);

    }

  /* If last block's header's size or allocation bit is wrong,
   * the epilogue's header is wrong. We also check the specific location
   * of the epilogue header with respect to the last byte of the heap.
   * mem_heap_hi() and bp(at this point) both point to the same word,
   * but mem_heap_hi() points to the last byte and hence we must add 3 to
   * the address of the header of bp to check this condition.
   */
  if (GET_SIZE(HDRP(bp)) != 0 || (GET_ALLOC(HDRP(bp)) != 1)
      || (HDRP(bp) + WSIZE - 1) != mem_heap_hi())
    printf("Bad epilogue header\n");

  for(bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREE(bp))
    checkFreeNodes(bp);

}

/* The remaining routines are internal helper routines */

/*
 * checkFreeNodes - function that checks correctness of the blocks in
 * the free list
 */
static void checkFreeNodes(void *bp)
{
  /* Seperate condition for free_listp since it does not have a
   * previous pointer.
   */

  if(bp == free_listp)
    {
      /* Checking that free_listp indeed points to a free block. */
      if(GET_ALLOC(HDRP(bp)))
	printf("Error: Freelistp points to an allocated block.\n");

      /* Free_listp must point to a valid block and must not be
       * out of bounds */
      if(!(bp > mem_heap_lo() && bp < mem_heap_hi()))
	printf("Error: Free list pointer out of heap bounds.\n");

      /* Previous pointer of free_listp
       * must point nowhere (nil). */
      if(PREV_FREE(bp) != 0 )
	printf("Error: Free pointer is not null.\n");
      return;
    }

  /* Checking that bp is indeed pointing to a free block */
  if(GET_ALLOC(HDRP(bp)) != 0)
    printf("Error: There exists an allocated block in the free list.\n");

  /* Check that next and prev pointers in consecutive blocks are consistent
   * Next pointer of previous block points to current block and previous pointer
   * of next block points to current block */
  // Split one print statement into 2 to not cross the 80 character limit.
  if(PREV_FREE(bp) && NEXT_FREE(PREV_FREE(bp)) != bp)
    {
      printf("Error: Next pointer of previous free block ");
      printf("not pointing to current block.\n");
    }

  if(NEXT_FREE(bp) && PREV_FREE(NEXT_FREE(bp)) != bp)
    {
      printf("Error: Previous pointer of next free block ");
      printf("not pointing to current block.\n");
    }

  /* Check that coalescing was correct at the free block pointed to by
     bp. The previous and next blocks must both be allocated.*/
  if(!GET_ALLOC(HDRP(NEXT_BLKP(bp))) || !GET_ALLOC(HDRP(PREV_BLKP(bp))))
    printf("Error: Contiguous free blocks in the heap\n");


}

/*
 * checkInFreeList - checks that all free blocks are in the free list
 * This function checks if the free block pointed to by bp is in the free list.
 * By calling this function from mm_checkheap(int) everytime we come across a
 * free block we will get to know if it is definitely in the free list or not.
 * We just go to the previous free block and if we do not reach the free list
 * pointer, then we know the free block is not in the free list.
*/
static void checkInFreeList(void *bp)
{
  void *temp = bp;
  if(temp == free_listp)
    return;
  while((temp = PREV_FREE(temp)) != 0)
    {
      if(temp == free_listp)
	return;
    }
}

/*
 * checkblock - checks basic invariants of a block in the heap list
 */
static void checkblock(void *bp)
{
  /* Checking for double word alignment */
  if ((size_t)bp % 8)
    printf("Error: %p is not doubleword aligned\n", bp);

  /* Header must match footer for allocation bit and size */
  if (GET(HDRP(bp)) != GET(FTRP(bp)))
    printf("Error: header does not match footer\n");

  /* Block pointer must be within the heap boundaries */
  if(bp > mem_heap_hi() || bp < mem_heap_lo())
    printf("Error: block pointer not within heap boundaries.\n");
}
/*
 * printblock
 */
static void printblock(void *bp)
{
  size_t hsize, halloc, fsize, falloc;

  hsize = GET_SIZE(HDRP(bp));
  halloc = GET_ALLOC(HDRP(bp));
  fsize = GET_SIZE(FTRP(bp));
  falloc = GET_ALLOC(FTRP(bp));

  if (hsize == 0) {
    printf("%p: EOL\n", bp);
    return;
  }

}

/*
 * extendHeap - extends the heap by 'words' bytes
 * The size is first aligned and using mem_sbrk we extend the heap and
 * get a pointer to the first word of the new part of the heap. We then
 * change the position fo the free block header and footer as well as the
 * epilogue header. We then coalesce with any free block(that was probably
 * too small for a requested size) present in front of the new part of the
 * heap.
 */
static void *extendHeap(size_t words)
{
  char *bp;
  size_t size;

  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words+1) * (WSIZE) : words * (WSIZE);

  if (size < MINBLOCKSIZE)
    size = MINBLOCKSIZE;

  /* If memory could not be obtained on the heap. */
  if ((long)(bp = mem_sbrk(size)) == -1)
    return NULL;

  /* Initialize free block header/footer and the epilogue header */
  PUT(HDRP(bp), PACK(size, 0));         /* free block header */
  PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

  /* Coalesce if the previous block was free and add the block to
   * the free list */
  return coalesce(bp);
}

/*
 * place - Allocates a block pointer to by bp with asize bytes.
 * If the free block can be split to form another free block that
 * has a size greater than MINBLOCKSIZE then we must set that block
 * to a free state and change it's size and also set the current block.
 * If the free block cannot be split in such a way, then we will have
 * to endure some internal fragmentation.
 */
static void place(void *bp, size_t asize)
{
  /* Gets the size of the whole free block that was at bp*/
  size_t freeBlkSize = GET_SIZE(HDRP(bp));

  /* Next block has size greater than or equal to MINBLOCKSIZE */
  if ((freeBlkSize - asize) >= MINBLOCKSIZE)
    {
      PUT(HDRP(bp), PACK(asize, 1));
      PUT(FTRP(bp), PACK(asize, 1));
      delBlkFromFreeList(bp);
      bp = NEXT_BLKP(bp);
      PUT(HDRP(bp), PACK(freeBlkSize-asize, 0));
      PUT(FTRP(bp), PACK(freeBlkSize-asize, 0));
      coalesce(bp);
    }

  /* If the remaining space is not enough for a free block,
   * then we have internal fragmentation which we can
   * do nothing about. Hence, don't split the block */
  else {
    PUT(HDRP(bp), PACK(freeBlkSize, 1));
    PUT(FTRP(bp), PACK(freeBlkSize, 1));
    delBlkFromFreeList(bp);
  }
}

/*
 * findFit
 * findFit finds a free block that has size at least asize bytes.
 * It uses an algorithm that is a slight combination of best fit
 * and first fit. The function traverses the list from the free_listp
 * and once it hits a free block of large enough size we traverse a
 * CONSTANT number of times. I used trial and error to find a constant
 * that would give me the most throughput.
 */
static void *findFit(size_t asize)
{
  void *bp = NULL;
  void *temp = free_listp;
  size_t minSize = mem_heapsize(); // maximum size
  /* First fit search */
  size_t size;
  int counter = 0;  /* counter for CONSTANT number of traversals */
  int flag = 0;     /* flag is set if we come across a fit. */

  while(!GET_ALLOC(HDRP(temp)))  /* While we are pointing to a free block */
    {
      if(asize <= (size = (size_t)GET_SIZE(HDRP(temp))) && size < minSize)
	{
	  /* If we have a block that fits perfectly,
	   * then there is no point in searching for
	   * a smaller block because we have found the smallest possible one
	   */
	  if(asize == size)
	    return temp;

	  bp = temp;
	  minSize = size;
	  flag = 1;
	}

      if(flag == 1)
	counter++;

      /* We have traversed enough. */
      if(counter == CONSTANT)
	return bp;

      temp = NEXT_FREE(temp);
    }
  return bp;
}

/*
 * insertAtFront - Inserts a block pointed to
 * by bp at the front of the free list
 * (LIFO policy)
 */
static void insertAtFront(void *bp)
{
  /* Make the next pointer of the block point to
   * start of the list i.e. free_listp */
  NEXT_FREE(bp) = free_listp;

  /* Previous pointer of bp should not point
   * anywhere. Set to 0 */
  PREV_FREE(bp) = 0;

  /* Set free_list prev to point to bp.
   * This is how we include bp into the list.
   * Since free_listp must always point to the
   * first free block, and bp is the first free block,
   * we set free_listp = bp */
  PREV_FREE(free_listp) = bp;
  free_listp = bp;
}

/*
 * delBlkFromFreeList - Removes a block from the free list
 * This function takes a block pointer of the block to remove, as a
 * parameter. This is basically a rearrangement of the next
 * and prev pointers.
 */
static void delBlkFromFreeList(void *bp)
{
  if (bp == free_listp)
    free_listp = NEXT_FREE(bp);
  else
    /* Set next pointer of previous free block
     * to point to the next block(thereby skipping the current
     * block). */
    NEXT_FREE(PREV_FREE(bp)) = NEXT_FREE(bp);
  /* The previous pointer of the next block points to
   * the previous block thereby skipping the current block. */
  PREV_FREE(NEXT_FREE(bp)) = PREV_FREE(bp);
}
