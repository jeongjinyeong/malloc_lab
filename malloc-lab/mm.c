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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "Test",
    /* Second member's email address (leave blank if none) */
    "test@cs.cmu.edu"
};

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE   (1<<6) /* Extend heap by this amount (bytes) */

#define MAX(x,y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, prev_in_use)   ((size) | (prev_in_use))

/* Read and write a word at address p */
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)         (GET(p) & ~0b111)
#define GET_PREV_SIZE(p)    (GET_SIZE((p) - DSIZE))
//#define GET_ALLOC(p)        (GET(p) & 0b1)
#define GET_PREV_IN_USE(p)  (GET(p) & 0b001)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define FD(bp)          (*(chunk **)(bp))
#define BK(bp)          (*(chunk **)((char *)(bp) + DSIZE))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)   (chunk *)((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp)   (chunk *)((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0b111)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*
*  3 ~  7 : 단일 크기 리스트(24 ~ 56 바이트)
*  8 ~ 13 : (64    ~ 248   바이트)
* 14 ~ 19 : (256   ~ 1016  바이트)
* 20 ~ 25 : (1024  ~ 4088  바이트)
* 26 ~ 31 : (4096  ~ 16376 바이트)
* 32 ~ 33 : (16384 ~ 32760 바이트)
* 34      : (32768 ~       바이트)
*/ 
#define IDX(size)                           \
    ((size) < 64    ? ((size) / 8)        : \
     (size) < 256   ? ((size) >> 5)  +  6 : \
     (size) < 1024  ? ((size) >> 7)  + 12 : \
     (size) < 4096  ? ((size) >> 9)  + 18 : \
     (size) < 16384 ? ((size) >> 11) + 24 : \
     (size) < 32768 ? ((size) >> 13) + 30 : 34)

typedef struct _Chunk{
    struct _Chunk *fd;
    struct _Chunk *bk;
}chunk;

typedef struct{
    chunk *bins[35];
}Arena;

static Arena *arena;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
void *mm_malloc(size_t size);
void place(void *bp, size_t size);
void *find_fit(size_t size);

/* Put chunk into free list */
void put_chunk(void *bp){
    size_t idx = IDX(GET_SIZE(HDRP(bp)));
    BK(bp) = arena->bins[idx];
    FD(bp) = NULL;
    if(arena->bins[idx])
        FD(arena->bins[idx]) = bp;
    arena->bins[idx] = bp;
}

void put_chunk_address_ordered(void *bp){
    size_t idx = IDX(GET_SIZE(HDRP(bp)));
    chunk *cur = arena->bins[idx];
    if(cur && (unsigned long long)cur < (unsigned long long)bp){
        while(BK(cur) && (unsigned long long)BK(cur) < (unsigned long long)bp){
            cur = cur->bk;
        }
        FD(bp) = cur;
        BK(bp) = BK(cur);
        if(BK(cur))
            FD(BK(cur)) = bp;
        BK(cur) = bp;
    }
    else{
        BK(bp) = cur;
        FD(bp) = NULL;
        if(cur)
            FD(cur) = bp;
        arena->bins[idx] = bp;
    }
}

/* Get chunk from free list */
void get_chunk(void *bp){
    size_t idx = IDX(GET_SIZE(HDRP(bp)));
    if(arena->bins[idx]==bp)
        arena->bins[idx] = BK(bp);
    if(FD(bp))
        BK(FD(bp)) = BK(bp);
    if(BK(bp))
        FD(BK(bp)) = FD(bp);
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    arena = (Arena *)mem_sbrk(35 * sizeof(chunk));

    for(size_t i = 0; i <= 34; i++){
        arena->bins[i] = NULL;
    }
    
    void *brk = (void *)-1;
    if((brk = mem_sbrk(2*WSIZE)) == (void *)-1)
        return -1;
    
    PUT(brk, PACK(WSIZE, 0));
    PUT(brk + WSIZE, PACK(0,1));
    
    chunk *bp;
    if((bp = extend_heap(CHUNKSIZE/WSIZE)) == NULL)
        return -1;

    return 0;
}

static void *extend_heap(size_t words){
    chunk *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, GET_PREV_IN_USE(HDRP(bp)))); /////// 헤더 플래그 작성할 때 HDRP(NEXT_BLKP(bp))로 초기화했는데 아직 값을 쓰기 전이라 HDRP(bp)로 수정함.
    PUT(FTRP(bp), size);
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 0));

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_PREV_IN_USE(HDRP(bp));
    size_t next_alloc = 1;
    if(GET_SIZE(HDRP(NEXT_BLKP(bp))))
        next_alloc = GET_PREV_IN_USE(HDRP(NEXT_BLKP(NEXT_BLKP(bp))));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){
        put_chunk_address_ordered(bp);
    }
    else if(!next_alloc){
        get_chunk(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, prev_alloc));
        PUT(FTRP(bp), size);
        put_chunk_address_ordered(bp);
    }
    else if(!prev_alloc){
        get_chunk(PREV_BLKP(bp));
        size += GET_PREV_SIZE(bp);
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, GET_PREV_IN_USE(HDRP(PREV_BLKP(bp)))));
        PUT(FTRP(PREV_BLKP(bp)), size);
        bp = PREV_BLKP(bp);
        put_chunk_address_ordered(bp);
    }
    else{
        get_chunk(PREV_BLKP(bp));
        get_chunk(NEXT_BLKP(bp));
        size += GET_PREV_SIZE(bp)+GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, GET_PREV_IN_USE(HDRP(PREV_BLKP(bp)))));
        PUT(FTRP(PREV_BLKP(bp)), size);
        bp = PREV_BLKP(bp);
        put_chunk_address_ordered(bp);
    }
    return bp;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    chunk *bp;
    size_t asize;       /* Adjusted block size */
    size_t extendsize;  /* Amount to extend heap if no fit */

    /* Ignore spurious requests */
    if(size == 0)
        return NULL;
    
    /* Adjust block size to include overhead and alignment reqs */
    if(size <= 2 * DSIZE)
        asize = 3 * DSIZE;
    else
        asize = DSIZE * ((size + DSIZE + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;
}

void *find_fit(size_t size){
    size_t idx = IDX(size);
    
    while(idx <= 34){
        chunk *cur = arena->bins[idx];
        while(cur){
            if(GET_SIZE(HDRP(cur)) >= size){
                return cur;
            }
            cur = cur->bk;
        }
        idx++;
    }
    return NULL;
}

void place(void *bp, size_t size){
    size_t asize = size;
    size_t blk_size = GET_SIZE(HDRP(bp));

    if(blk_size - size < 2*WSIZE + 2*DSIZE){  // 남은 블록이 최소 블록 크기를 맞추지 못 하는 경우
        get_chunk(bp);
        asize = blk_size; // 할당하는 블록에 전체 블록 할당
        PUT(HDRP(bp), PACK(asize, GET_PREV_IN_USE(HDRP(bp))));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 0b001));
    }
    else{
        get_chunk(bp);
        PUT(HDRP(bp), PACK(asize, GET_PREV_IN_USE(HDRP(bp))));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(blk_size-asize, 0b001));
        PUT(FTRP(NEXT_BLKP(bp)), blk_size-asize);
        coalesce(NEXT_BLKP(bp));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(FTRP(ptr), size);
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(GET_SIZE(HDRP(NEXT_BLKP(ptr))), 0b000));
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
    size_t oldSize = GET_SIZE(HDRP(ptr));
    size_t asize = ALIGN(size+WSIZE);
    
    if(oldSize>=asize){ // 줄어드는 경우
        if(oldSize - asize < 2*WSIZE + 2*DSIZE){
            newptr = ptr;
        }
        else{
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(GET_SIZE(HDRP(NEXT_BLKP(ptr))), 0b000));
            PUT(HDRP(ptr), PACK(asize, GET_PREV_IN_USE(HDRP(ptr))));
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(oldSize-asize, 0b001));
            PUT(FTRP(NEXT_BLKP(ptr)), oldSize-asize);
            coalesce(NEXT_BLKP(ptr));
            newptr = ptr;
        }
        return newptr;
    }
    
    size_t blkSize = GET_SIZE(HDRP(ptr))+GET_SIZE(HDRP(NEXT_BLKP(ptr)));    
    if(GET_SIZE(HDRP(NEXT_BLKP(ptr)))&&!GET_PREV_IN_USE(HDRP(NEXT_BLKP(NEXT_BLKP(ptr))))){ // 늘어날 공간이 있는 경우
        if(blkSize >= asize){
            newptr = ptr;
            if(blkSize - asize >= (2*WSIZE + 2*DSIZE)){ // 남은 블록이 최소 블록 크기 만족하는 경우
                get_chunk(NEXT_BLKP(ptr));
                PUT(HDRP(ptr), PACK(asize, GET_PREV_IN_USE(HDRP(ptr))));
                PUT(HDRP(NEXT_BLKP(ptr)), PACK(blkSize-asize, 0b001));
                PUT(FTRP(NEXT_BLKP(ptr)), blkSize-asize);
                coalesce(NEXT_BLKP(ptr));
            }
            else{ // 남은 블록이 최소 블록 크기 만족 못하는 경우
                get_chunk(NEXT_BLKP(ptr));
                PUT(HDRP(ptr), PACK(blkSize, GET_PREV_IN_USE(HDRP(ptr))));
                PUT(HDRP(NEXT_BLKP(ptr)), PACK(GET_SIZE(HDRP(NEXT_BLKP(ptr))), 0b001));
            }
        }
        else{ // 늘어날 공간이 부족해 새로운 공간을 할당해야 하는 경우
            if(!GET_SIZE(HDRP(NEXT_BLKP(NEXT_BLKP(ptr))))){ // 부족한 여유 공간 뒤가 에필로그인 경우
                chunk *bp;
                size_t extendsize;

                extendsize = MAX(asize-blkSize, CHUNKSIZE);
                if((bp = extend_heap(extendsize/WSIZE)) == NULL){
                    return NULL;
                }
                get_chunk(NEXT_BLKP(ptr));
                newptr = ptr;
                size_t remainSize = oldSize + GET_SIZE(HDRP(bp)) - asize;
                if(remainSize < 2*WSIZE + 2*DSIZE){
                    asize = oldSize + GET_SIZE(HDRP(bp));
                    remainSize = 0;
                }
                PUT(HDRP(ptr), PACK(asize, GET_PREV_IN_USE(HDRP(ptr))));
                PUT(HDRP(NEXT_BLKP(ptr)), PACK(remainSize, 0b001));
                if(remainSize){
                    PUT(FTRP(NEXT_BLKP(ptr)), remainSize);
                    PUT(HDRP(NEXT_BLKP(NEXT_BLKP(ptr))), PACK(0, 0));
                    coalesce(NEXT_BLKP(ptr));
                }else{
                    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));
                }
            }
            else{
                newptr = mm_malloc(asize);
                if(newptr == NULL)
                    return NULL;
                copySize = oldSize - WSIZE;
                if (size < copySize)
                    copySize = size;
                memcpy(newptr, oldptr, copySize);
                mm_free(oldptr);
            }
        }
    }
    else{
        if(!GET_SIZE(HDRP(NEXT_BLKP(ptr)))){
            chunk *bp;
            size_t extendsize;

            extendsize = MAX(asize-blkSize, CHUNKSIZE);
            if((bp = extend_heap(extendsize/WSIZE)) == NULL){
                return NULL;
            }
            get_chunk(NEXT_BLKP(ptr));
            newptr = ptr;
            size_t remainSize = oldSize + GET_SIZE(HDRP(bp)) - asize;
            if(remainSize < 2*WSIZE + 2*DSIZE){
                asize = oldSize + GET_SIZE(HDRP(bp));
                remainSize = 0;
            }
            PUT(HDRP(ptr), PACK(asize, GET_PREV_IN_USE(HDRP(ptr))));
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(remainSize, 0b001));
            if(remainSize){
                PUT(FTRP(NEXT_BLKP(ptr)), remainSize);
                PUT(HDRP(NEXT_BLKP(NEXT_BLKP(ptr))), PACK(0, 0));
                coalesce(NEXT_BLKP(ptr));
            }else{
                PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));
            }
        }
        else{
            newptr = mm_malloc(asize);
            if(newptr == NULL)
                return NULL;
            copySize = oldSize - WSIZE;
            if (size < copySize)
                copySize = size;
            memcpy(newptr, oldptr, copySize);
            mm_free(oldptr);
        }
    }
    return newptr;
}