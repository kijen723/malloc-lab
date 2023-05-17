/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "KJ_2",
    /* First member's full name */
    "Kim InJe",
    /* First member's email address */
    "kij2646@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros*/
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)
#define LISTLIMIT 20

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define NEXT_P(bp) (*(void **)(bp))
#define PREV_P(bp) (*(void **)((bp) + WSIZE))

static void *heap_listp;
static void *s_list[LISTLIMIT];
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void list_add(void *bp, size_t size);
static void list_remove(void *bp);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    int list;

    for (list = 0; list < LISTLIMIT; list++) {
        s_list[list] = NULL;
    }

    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) {
        return -1;
    }

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE);

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1;
    }

    return 0;
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        list_add(bp, size);
        return bp;
    } else if (prev_alloc && !next_alloc) {
        list_remove(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        list_remove(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {
        list_remove(PREV_BLKP(bp));
        list_remove(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        
    }

    list_add(bp, size);
    return bp;
}

static void *find_fit(size_t asize) {
    void *bp;
    int list = 0;
    size_t searchsize = asize;

    while (list < LISTLIMIT) {
        if ((list == LISTLIMIT - 1) || (searchsize <= 1) && (s_list[list] != NULL)) {
            bp = s_list[list];

            while ((bp != NULL) && (asize > GET_SIZE(HDRP(bp)))) {
                bp = PREV_P(bp);
            }

            if (bp != NULL) {
                return bp;
            }
        }

        searchsize >>= 1;
        list++;
    }

    return NULL;
}

static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    list_remove(bp);

    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        coalesce(bp);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void list_add(void *bp, size_t size){
    int list = 0;
    void *search_ptr;
    void *insert_ptr = NULL;

    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }

    search_ptr = s_list[list];

    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
        insert_ptr = search_ptr;
        search_ptr = PREV_P(search_ptr);
    }

    if (search_ptr != NULL) {
        if (insert_ptr != NULL) {
            PREV_P(bp) = search_ptr;
            NEXT_P(bp) = insert_ptr;
            NEXT_P(search_ptr) = bp;
            PREV_P(insert_ptr) = bp;
        } else {
            PREV_P(bp) = search_ptr;
            NEXT_P(bp) = NULL;
            NEXT_P(search_ptr) = bp;
            s_list[list] = bp;
        }
    } else {
        if (insert_ptr != NULL) {
            PREV_P(bp) = NULL;
            NEXT_P(bp) = insert_ptr;
            PREV_P(insert_ptr) = bp;
        } else {
            PREV_P(bp) = NULL;
            NEXT_P(bp) = NULL;
            s_list[list] = bp;
        }
    }
}

static void list_remove(void *bp){
    int list = 0;
    size_t size = GET_SIZE(HDRP(bp));

    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }

    if (PREV_P(bp) != NULL) {
        if (NEXT_P(bp) != NULL) {
            NEXT_P(PREV_P(bp)) = NEXT_P(bp);
            PREV_P(NEXT_P(bp)) = PREV_P(bp);
        } else {
            NEXT_P(PREV_P(bp)) = NULL;
            s_list[list] = PREV_P(bp);
        } 
    } else {
        if (NEXT_P(bp) != NULL) {
            PREV_P(NEXT_P(bp)) = NULL;
        } else {
            s_list[list] = NULL;
        }
    }

    return;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    int asize = ALIGN(size + SIZE_T_SIZE);
    size_t extendsize;
    char *bp;

    if (size == 0) {
        return NULL;
    }

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}