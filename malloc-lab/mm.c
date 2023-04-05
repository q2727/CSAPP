/*
 * Simple, 32-bit and 64-bit clean allocator based on implicit free
 * lists, first-fit placement, and boundary tag coalescing, as described
 * in the CS:APP3e text. Blocks must be aligned to doubleword (8 byte)
 * boundaries. Minimum block size is 16 bytes.
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
        /* Team name */
        "ateam",
        /* First member's full name */
        "QC",
        /* First member's email address */
        "wuyiwuhha@gmail.com",
        /* Second member's full name (leave blank if none) */
        "",
        /* Second member's email address (leave blank if none) */
        ""
};
/*
 * If NEXT_FIT defined use next fit search, else use first-fit search
 */
#define NEXT_FITx

void *listArr[29] = {NULL};
#define MIDSIZE  72
#define DEBUGx
/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ //line:vm:mm:beginconst
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  ((1<<12)+60)  /* Extend heap by this amount (bytes) */  //line:vm:mm:endconst

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc, prev_alloc)  ((size) | (alloc) | (prev_alloc << 1)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            //line:vm:mm:get
#define PUT(p, val)  (*(unsigned int *)(p) = (val))
#define GET_PREV_ALLOC(p) ((GET(p) >> 1) & 0x1) //line:vm:mm:put
#define PUTPRE(p, ptr) ((*(void**)(p)) = ptr)
#define PUTSUC(p, ptr) ((*((void**)(p)+1)) = ptr)
#define GETPRE(p) (*(void**)(p))
#define GETSUC(p) (*((void**)(p)+1))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)                    //line:vm:mm:getalloc

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      //line:vm:mm:hdrp
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //line:vm:mm:ftrp

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //line:vm:mm:nextblkp
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //line:vm:mm:prevblkp
/* $end mallocmacros */

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
#ifdef NEXT_FIT
static char *rover;           /* Next fit rover */
#endif

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);

static void place(void *bp, size_t asize);

static void *find_fit(size_t asize);

static void *coalesce(void *bp);

static void printblock(void *bp);

static void checkheap(int verbose);

static void checkblock(void *bp);

static void printBlock();

static void addList(void *bp);

static void delList(void *bp);

/*
 * mm_init - Initialize the memory manager
 */
/* $begin mminit */
int mm_init(void) {
    FILE *fp = fopen("out.txt", "w");
    fprintf(fp, "");
    fclose(fp);
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) -1) //line:vm:mm:begininit
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1, 1));     /* Epilogue header */     /* Epilogue header */
    heap_listp += (2 * WSIZE);
    for (int i = 0; i < 29; i++) {
        listArr[i] = NULL;
    }//line:vm:mm:endinit
    /* $end mminit */
#ifdef NEXT_FIT
    rover = heap_listp;
#endif
    /* $begin mminit */

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}
/* $end mminit */

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) {
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;
    /* $end mmmalloc */
    if (heap_listp == 0) {
        mm_init();
    }
    /* $begin mmmalloc */
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= 3 * WSIZE)                                          //line:vm:mm:sizeadjust1
        asize = 2 * DSIZE;                                        //line:vm:mm:sizeadjust2
    else
        asize = DSIZE * ((size + (WSIZE) + (DSIZE - 1)) / DSIZE); //line:vm:mm:sizeadjust3

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  //line:vm:mm:findfitcall
        size_t csize = GET_SIZE(HDRP(bp));
        place(bp, asize);                  //line:vm:mm:findfitplace
#ifdef DEBUG
        printBlock();
#else
#endif
        if ((asize > MIDSIZE) && ((csize - asize) >= (2 * DSIZE))) {
            return (void *) ((char *) bp + csize - asize);
        }
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);                 //line:vm:mm:growheap1
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;//line:vm:mm:growheap2
    size_t csize = GET_SIZE(HDRP(bp));
    place(bp, asize);
//    FILE *fp= fopen("out.txt","a");
//    fprintf(fp,"extended: ");
//    fclose(fp);
#ifdef DEBUG
    printf("extend: ");
    printBlock();//line:vm:mm:growheap3
#else
#endif
    if ((asize > MIDSIZE) && ((csize - asize) >= (2 * DSIZE))) {
        return (void *) ((char *) bp + csize - asize);
    }
    return bp;
}
/* $end mmmalloc */

/*
 * mm_free - Free a block
 */
/* $begin mmfree */
void mm_free(void *bp) {
    /* $end mmfree */
    if (bp == 0)
        return;

    /* $begin mmfree */
    size_t size = GET_SIZE(HDRP(bp));
    /* $end mmfree */
    if (heap_listp == 0) {
        mm_init();
    }
    /* $begin mmfree */

    PUT(HDRP(bp), PACK(size, 0, GET_PREV_ALLOC(HDRP(bp))));
    PUT(FTRP(bp), PACK(size, 0, GET_PREV_ALLOC(HDRP(bp))));

    if (GET_ALLOC(HDRP(NEXT_BLKP(bp)))) {
        PUT(HDRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 1, 0));

    } else {
        PUT(HDRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 0, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 0, 0));
    }
    coalesce(bp);
#ifdef DEBUG
    printBlock();
#else
#endif
}

/* $end mmfree */
/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
/* $begin mmfree */
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        PUT(HDRP(bp), PACK(size, 0, 1));
        PUT(FTRP(bp), PACK(size, 0, 1));
        addList(bp);                             /* Case 1 */
    } else if (prev_alloc && !next_alloc) {/* Case 2 */
        delList(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0, 1));
        PUT(FTRP(bp), PACK(size, 0, 1));
        addList(bp);
    } else if (!prev_alloc && next_alloc) {      /* Case 3 */
        delList(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0, 1));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0, 1));
        bp = PREV_BLKP(bp);
        addList(bp);
    } else {                                     /* Case 4 */
        delList(PREV_BLKP(bp));
        delList(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0, 1));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0, 1));
        bp = PREV_BLKP(bp);
        addList(bp);
    }
    /* $end mmfree */
#ifdef NEXT_FIT
    /* Make sure the rover isn't pointing into the free block */
    /* that we just coalesced */
    if ((rover > (char *)bp) && (rover < NEXT_BLKP(bp)))
        rover = bp;
#endif
    /* $begin mmfree */
    return bp;
}
/* $end mmfree */

/*
 * mm_realloc - Naive implementation of realloc
 */
void *mm_realloc(void *ptr, size_t size) {
    size_t oldsize;
    void *newptr = NULL;

    //size= MAX(size,(28100));
    oldsize = GET_SIZE(HDRP(ptr));
    /* If size == 0 then this is just free, and we return NULL. */
    if (size == 0) {
        mm_free(ptr);
        return 0;
    }
    /* If oldptr is NULL, then this is just malloc. */
    if (ptr == NULL) {
        newptr = mm_malloc(size);
        if (newptr == NULL) {
            return NULL;
        }
    }
    size_t asize = 0;
    if (size <= 3 * WSIZE) {                                     //line:vm:mm:sizeadjust1
        asize = 2 * DSIZE;
    } else {
        asize = DSIZE * ((size + (WSIZE) + (DSIZE - 1)) / DSIZE);
    }//line:vm:mm:sizeadjust3
    if (((int) oldsize - (int) asize) >= (2 * DSIZE)) {
        newptr = ptr;
        PUT(HDRP(ptr), PACK(asize, 1, GET_PREV_ALLOC(HDRP(ptr))));
        ptr = NEXT_BLKP(ptr);
        PUT(HDRP(ptr), PACK(oldsize - asize, 0, 1));
        PUT(FTRP(ptr), PACK(oldsize - asize, 0, 1));
        coalesce(ptr);
    } else if (((int) oldsize - (int) asize) < 0) {
        size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        if ((GET_ALLOC(HDRP(NEXT_BLKP(ptr))) == 0) && ((asize - oldsize) <= next_size)) {
            newptr = ptr;
            delList(NEXT_BLKP(ptr));
            if ((next_size - asize + oldsize) >= (2 * DSIZE)) {
                PUT(HDRP(ptr), PACK(asize, 1, GET_PREV_ALLOC(HDRP(ptr))));
                PUT(HDRP(NEXT_BLKP(ptr)), PACK((next_size - asize + oldsize), 0, 1));
                PUT(FTRP(NEXT_BLKP(ptr)), PACK((next_size - asize + oldsize), 0, 1));
                addList(NEXT_BLKP(ptr));
            } else {
                PUT(HDRP(ptr), PACK(oldsize + next_size, 1, GET_PREV_ALLOC(HDRP(ptr))));
                PUT(HDRP(NEXT_BLKP(ptr)), PACK(GET_SIZE(HDRP(NEXT_BLKP(ptr))), 1, 1));
            }
        } else {
#ifdef DEBUG
            printf("realloc: ");
#endif
            newptr = mm_malloc(size);
            /* If realloc() fails the original block is left untouched  */
            if (!newptr) {
                return 0;
            }
            /* Copy the old data. */
            oldsize -= 4;
            if (size < oldsize) oldsize = size;
            memcpy(newptr, ptr, oldsize);
            /* Free the old block. */
            mm_free(ptr);
        }
    } else {
        newptr = ptr;
        PUT(HDRP(ptr), PACK(oldsize, 1, GET_PREV_ALLOC(HDRP(ptr))));
    }
#ifdef DEBUG
    printBlock();
#endif
    return newptr;
}

/*
 * mm_checkheap - Check the heap for correctness
 */
//void *mm_realloc(void *ptr, size_t size)
//{
//    size_t oldsize;
//    void *newptr;
//
//    /* If size == 0 then this is just free, and we return NULL. */
//    if(size == 0) {
//        mm_free(ptr);
//        return 0;
//    }
//
//    /* If oldptr is NULL, then this is just malloc. */
//    if(ptr == NULL) {
//        return mm_malloc(size);
//    }
//
//    newptr = mm_malloc(size);
//
//    /* If realloc() fails the original block is left untouched  */
//    if(!newptr) {
//        return 0;
//    }
//
//    /* Copy the old data. */
//    oldsize = GET_SIZE(HDRP(ptr));
//    if(size < oldsize) oldsize = size;
//    memcpy(newptr, ptr, oldsize);
//
//    /* Free the old block. */
//    mm_free(ptr);
//
//    return newptr;
//}

void mm_checkheap(int verbose) {
    checkheap(verbose);
}

/*
 * The remaining routines are internal helper routines
 */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; //line:vm:mm:beginextend
    if ((long) (bp = mem_sbrk(size)) == -1)
        return NULL;                                        //line:vm:mm:endextend

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0, GET_PREV_ALLOC(HDRP(bp))));         /* Free block header */   //line:vm:mm:freeblockhdr
    PUT(FTRP(bp), PACK(size, 0, GET_PREV_ALLOC(HDRP(bp))));         /* Free block footer */   //line:vm:mm:freeblockftr
    PUT(HDRP(NEXT_BLKP(bp)),
        PACK(0, 1, 0)); /* New epilogue header */ //line:vm:mm:newepihdr/* New epilogue header */ //line:vm:mm:newepihdr
    /* Coalesce if the previous block was free */
    return coalesce(bp);                                          //line:vm:mm:returnblock
}
/* $end mmextendheap */

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    size_t csize = GET_SIZE(HDRP(bp));
    if ((csize - asize) >= (2 * DSIZE)) {
        if (asize <= MIDSIZE) {
            delList(bp);
            PUT(HDRP(bp), PACK(asize, 1, 1));
            bp = NEXT_BLKP(bp);
            PUT(HDRP(bp), PACK(csize - asize, 0, 1));
            PUT(FTRP(bp), PACK(csize - asize, 0, 1));
            addList(bp);
        } else {
            delList(bp);
            PUT(HDRP((char *) bp + csize - asize), PACK(asize, 1, 0));
            PUT(HDRP(NEXT_BLKP((char *) bp + csize - asize)),
                PACK(GET_SIZE(HDRP(NEXT_BLKP((char *) bp + csize - asize))), 1, 1));
            PUT(HDRP(bp), PACK(csize - asize, 0, 1));
            PUT(FTRP(bp), PACK(csize - asize, 0, 1));
            addList(bp);
        }
    } else {
        delList(bp);
        PUT(HDRP(bp), PACK(csize, 1, 1));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 1, 1));
    }
}
/* $end mmplace */

/*
 * find_fit - Find a fit for a block with asize bytes
 */
/* $begin mmfirstfit */
/* $begin mmfirstfit-proto */
static void *find_fit(size_t asize)
/* $end mmfirstfit-proto */
{
    /* $end mmfirstfit */

#ifdef NEXT_FIT
    /* Next fit search */
    char *oldrover = rover;

    /* Search from the rover to the end of list */
    for ( ; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    /* search from start of list to old rover */
    for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    return NULL;  /* no fi 你  t found */
#else
    /* $begin mmfirstfit */
    /* First-fit search */

    int bitCount = 0;
    int tmp = asize;
    while (tmp != 0) {
        bitCount++;
        tmp >>= 1;
    }
    if (bitCount < 4)
        bitCount = 4;
    bitCount -= 4;
    void *p = listArr[bitCount];
    while (1) {
        while (p != NULL) {
            if (asize <= GET_SIZE(HDRP(p))) {
                return p;
            } else
                p = GETSUC(p);
        }
        if (p == NULL) {
            if (bitCount < 28) {
                bitCount++;
                p = listArr[bitCount];
            } else
                return NULL;
        }
    }
#endif
}

/* $end mmfirstfit */

static void printblock(void *bp) {
    size_t hsize, halloc, fsize, falloc;

    checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp,
           hsize, (halloc ? 'a' : 'f'),
           fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(void *bp) {
    if ((size_t) bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

/*
 * checkheap - Minimal check of the heap for consistency
 */
void checkheap(int verbose) {
    char *bp = heap_listp;

    if (verbose)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose)
            printblock(bp);
        checkblock(bp);
    }
    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
    return;
}

void printBlock() {
    //* fp= fopen("out.txt","a");
    for (int i = 0; i < 29; i++) {
        for (void *p = listArr[i]; p != NULL; p = GETSUC(p)) {
            //fprintf( fp,"%d: %d ", i, GET_SIZE(HDRP(p)));
            printf("%d: %d ", i, GET_SIZE(HDRP(p)));
        }
    }
    //fprintf(fp,"\n");
    printf("\n");
    //fclose(fp);
}

void addList(void *bp) {
    int size = GET_SIZE(HDRP(bp));
    int bitCount = 0;
    while (size != 0) {
        bitCount++;
        size >>= 1;
    }
    size = GET_SIZE(HDRP(bp));
    if (bitCount < 4)
        bitCount = 4;
    bitCount -= 4;
    if (listArr[bitCount] == NULL) {
        listArr[bitCount] = bp;
        PUTPRE(bp, NULL);
        PUTSUC(bp, NULL);
    } else if (size <= GET_SIZE(HDRP(listArr[bitCount]))) {
        PUTPRE(bp, NULL);
        PUTSUC(bp, listArr[bitCount]);
        PUTPRE(listArr[bitCount], bp);
        listArr[bitCount] = bp;
    } else {
        void *p;
        for (p = listArr[bitCount]; (GET_SIZE(HDRP(p)) < size) && GETSUC(p) != NULL; p = GETSUC(p)) {
        }
        if (GETSUC(p) == NULL && (GET_SIZE(HDRP(p)) < size)) {
            PUTSUC(p, bp);
            PUTPRE(bp, p);
            PUTSUC(bp, NULL);
        } else {
            PUTPRE(bp, GETPRE(p));
            PUTSUC(bp, p);
            PUTPRE(p, bp);
            PUTSUC(GETPRE(bp), bp);
        }
    }
}

void delList(void *bp) {
    int size = GET_SIZE(HDRP(bp));
    int bitCount = 0;
    while (size != 0) {
        bitCount++;
        size >>= 1;
    }
    if (bitCount < 4)
        bitCount = 4;
    bitCount -= 4;
    if ((!GETPRE(bp)) && (!GETSUC(bp))) {
        listArr[bitCount] = NULL;
    } else if ((!GETPRE(bp)) && (GETSUC(bp))) {
        listArr[bitCount] = GETSUC(bp);
        PUTPRE(listArr[bitCount], NULL);
    } else if ((GETPRE(bp)) && (!GETSUC(bp))) {
        PUTSUC(GETPRE(bp), NULL);
    } else if ((GETPRE(bp)) && (GETSUC(bp))) {
        PUTSUC(GETPRE(bp), GETSUC(bp));
        PUTPRE(GETSUC(bp), GETPRE(bp));
    }
}