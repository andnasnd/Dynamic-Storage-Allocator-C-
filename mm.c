/*
 ******************************************************************************
 *                               mm.c                                         *
 *           64-bit struct-based implicit free list memory allocator          *
 *                      without coalesce functionality                        *
 *                 CSE 361: Introduction to Computer Systems                  *
 *                          Anand Nambakam 450431
 *                                                                            *
 *  ************************************************************************  *
 *           64-bit struct-based segregated list memory allocator with        *
 *           coalesce functionality. Optimizations made were:                 *
 *             1. Reduce minimum block size from 32 to 16                     *
 *             2. "Small list" implemented as a heap for blocks <= min b_size *
 *             3. Regular segregated list for block sized > min block size    *
 *             4. Removed footers                                             *
 *             5. Best fit + Next fit                                         *
 *                                                                            *
 *           Also implemented debugging methods:                              *
 *             1. checkheap() - checks validity of heap                       *
 *             2. printheap() - prints heap                                   *
 *                                                                            *
 *                                                                            *
 *                                                                            *
 *  ************************************************************************  *
 *  ** ADVICE FOR STUDENTS. **                                                *
 *  Step 0: Please read the writeup!                                          *
 *  Step 1: Write your heap checker. Write. Heap. checker.                    *
 *  Step 2: Place your contracts / debugging assert statements.               *
 *  Good luck, and have fun!                                                  *
 *                                                                            *
 ******************************************************************************
 */

/* Do not change the following! */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
// #define DEBUG // uncomment this line to enable debugging

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) //printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*sizeof(word_t);       // double word size (bytes)
static const size_t min_block_size = 4*sizeof(word_t); // Minimum block size
static const size_t tiny_block_size = 2*sizeof(word_t);
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)
static const size_t numtinyblocks = 256 + 1; //+ 1, use first block for managing list

static const word_t alloc_mask = 0x1;
static const word_t prev_alloc_mask = 0x2; 
static const word_t min_alloc_mask = 0x4; 
static const word_t size_mask = ~(word_t)0xF;

typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    union
    {
        struct 
        {
             struct block* prev;
             struct block* next;
        } d;  
   
         /*
          * We don't know how big the payload will be.  Declaring it as an
          * array of size 0 allows computing its starting address using
          * pointer notation.
          */
         char payload[0];
    }; 
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
} block_t;

//for minimum block size, header is 
typedef struct minblock 
{
     union 
     {
          struct 
          {
               word_t header; 
               struct minblock* next;
          };
          char payload[0];
      };

} minblock_t;

typedef struct freelist
{
     block_t *head;
     block_t *tail; 

} freelist_t;

typedef enum 
{
     FREELIST_TYPE_16_32 = 0,
     FREELIST_TYPE_32_64,
     FREELIST_TYPE_64_128,
     FREELIST_TYPE_128_256,
     FREELIST_TYPE_256_512,
     FREELIST_TYPE_512_1024,
     FREELIST_TYPE_1024_2048,
     FREELIST_TYPE_2048_4096,
     FREELIST_TYPE_4096_8192,
     FREELIST_TYPE_8192_16384,
     FREELIST_TYPE_REG,
     FREELIST_TYPE_SENTINEL
 
} FREELIST_TYPE; 

/* Global variables */
/* Pointer to first block */
static block_t *heap_start = NULL;
/* Explicit Free List */
static freelist_t freelists[FREELIST_TYPE_SENTINEL];
static minblock_t *minfreelist = NULL;
static freelist_t minblocklist = {0}; 

bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *find_explicitfit(size_t asize);
static void add_tofreelist(block_t *block);
static void remove_fromfreelist(block_t *block);
static void print_freelist();
static void print_freelists();
static void print_heap();
static void set_prev_alloc(block_t *block, bool flag); 
static void set_min_alloc(block_t *block, bool flag); 
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc, bool prev_alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);
static FREELIST_TYPE get_free_list_type(size_t size); 

static bool is_min_block(void *bp); 
static bool extract_alloc(word_t header);
static bool extract_prev_alloc(word_t word);
static bool extract_min_alloc(word_t word);
static bool get_alloc(block_t *block);
static bool get_prev_alloc(block_t *block);
static bool get_min_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc, bool prev_alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);


/*
 * mm_init: initialize heap with prologue and epilogue, 
 * and initializes other globals that help keep track of
 * memory management
 */
bool mm_init(void) 
{
    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));
    int i;

    if (start == (void *)-1) 
    {
        return false;
    }

    start[0] = pack(0, true, false); // Prologue footer
    start[1] = pack(0, true, false); // Epilogue header

    // Heap starts with first "block header", currently the epilogue footer
    heap_start = (block_t *) &(start[1]);
    for (i = 0; i < FREELIST_TYPE_SENTINEL; i++)
    {
         freelists[i].head = NULL; 
         freelists[i].tail = NULL; 
    }
    minfreelist = NULL; 
    minblocklist.head = NULL;
    minblocklist.tail = NULL; 
    //printf("INIT EXTEND HEAP***\n");
    block_t* b = extend_heap(chunksize);
    //printf("extend_heap returned block %p\n", b);
    // Extend the empty heap with a free block of chunksize bytes
    if (b == NULL)
    {
        return false;
    }
    add_tofreelist(b);
    return true;
}

/*
 * malloc is called to allocate memory 
 */
void *malloc(size_t size) 
{
    //printf("malloc called with size=%ld\n", size);

#ifdef ENABLE_PRINT_HEAP
    print_heap(); 
#endif
    dbg_requires(mm_checkheap(__LINE__));
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_start == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap(__LINE__));

#ifdef ENABLE_PRINT_HEAP
        print_heap();
#endif
        return bp;
    }

    //printf("size: %ld, asize= %ld\n", size, asize); 
    // Search the free list for a fit
    if (size <= tiny_block_size)
    {
         minblock_t *minblock = NULL; 
         if (minfreelist == NULL)
         {
             //use the first tinyblock to maintain the list of minblocks
             size_t numblocks = numtinyblocks; 
             size_t i; 
             size_t blocksize = max((numblocks*tiny_block_size) + dsize, dsize); 
             block_t *block1 = find_explicitfit(blocksize); 
             if (block1 == NULL)
             {
                 extendsize = max(blocksize, chunksize); 
                 block1 = extend_heap(extendsize);
                 if (block1 == NULL)
                 {
#ifdef ENABLE_PRINT_HEAP
                     print_heap(); 
#endif
                     return bp; 
                 }
             }
             place(block1, blocksize); 
             set_min_alloc(block1, true);
             bp = header_to_payload(block1); 
             freelist_t *mb = (freelist_t*)bp; 
             mb->tail = NULL;
             mb->head = minblocklist.head; 
             minblocklist.head = block1;  

             //now have to subdivide block1 into minblocks
             //and insert them into minfreelist
             for (i = 1; i < numblocks; i++)
             {
                 minblock_t *b = (minblock_t *)(bp + i*tiny_block_size);
                 b->next = minfreelist; 
                 minfreelist = b;  
             }
         }
         minblock = minfreelist; 
         minfreelist = minfreelist->next; 
         bp = minblock; 
    }
    else 
    {
         // Adjust block size to include overhead and to meet alignment requirements
         asize = max(min_block_size, round_up(size + wsize, dsize));
         block = find_explicitfit(asize);

         // If no fit is found, request more memory, and then and place the block
         if (block == NULL)
         {  
             extendsize = max(asize, chunksize);
             block = extend_heap(extendsize);
             //printf("extend_heap returned block %p\n", block);
             if (block == NULL) // extend_heap returns an error
             {

#ifdef ENABLE_PRINT_HEAP
                  print_heap();
#endif
                  return bp;
             }
         }
         place(block, asize);
         bp = header_to_payload(block); 
    }

    dbg_ensures(mm_checkheap(__LINE__));

#ifdef ENABLE_PRINT_HEAP
    print_heap();
#endif
    return bp;
} 

/*
 * free a previously allocated memory that was obtained by calling malloc 
 */
void free(void *bp)
{
    //printf("Free called.");
#ifdef ENABLE_PRINT_HEAP
    print_heap(); 
#endif
    if (bp == NULL)
    {
        return;
    }

    if (is_min_block(bp))
    {
        minblock_t *minblock = (minblock_t *)bp; 
        minblock->next = minfreelist;
        minfreelist = minblock; 
    }
    else 
    {
        block_t *block = payload_to_header(bp);
        //printf(" Referencing block %p\n", block);
        size_t size = get_size(block);

        //preserve prev-alloc on current block
        bool prev_alloc = get_prev_alloc(block); 
        //set prev_alloc of current block 
        // size |= prev_alloc; 

        write_header(block, size, false, prev_alloc);
        write_footer(block, size, false);

        //set prev_alloc of subsequent block to 0 
        // find_next(block)->header &= (~prev_alloc_mask);
        set_prev_alloc(find_next(block), false);

        // since this block is just freed
        // we should set the d.prev and d.next to NULL
        block->d.prev = NULL;
        block->d.next = NULL;
        block_t* coalescedblock = coalesce(block);
        //printf("Coalesced block %p\n", coalescedblock); 
        add_tofreelist(coalescedblock);
    }
#ifdef ENABLE_PRINT_HEAP
    print_heap(); 
#endif
}

/*
 * resize a previously allocated memory obtained through malloc
 */
void *realloc(void *ptr, size_t size)
{
    //printf("Realloc called.\n");
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (newptr == NULL)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * calloc returns memory that is initialized to zero
 */
void *calloc(size_t elements, size_t size)
{
    //printf("Calloc called.\n");
    void *bp;
    size_t asize = elements * size;

    if (asize/elements != size)
    {    
        // Multiplication overflowed
        return NULL;
    }
    
    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * increases the size of the heap
 */
static block_t *extend_heap(size_t size) 
{
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);
    
    write_header(block, size, false, get_prev_alloc(block));
    write_footer(block, size, false);
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true, false);

    // Coalesce in case the previous block was free
    return coalesce(block);
}

/*
 * prints all the free lists. 
 * used for debugging 
 */
static void print_freelists()
{
    //printf("Free list:\n");
    int i;
    for (i = 0; i < FREELIST_TYPE_SENTINEL; i++)
    {
        //printf("%d==========\n",i);
        print_freelist(&freelists[i]); 
        //printf("==========\n");
    }
}

/*
 * print a given free list
 * used for debugging
 */
static void print_freelist(freelist_t* list)
{
    block_t* block;
    for (block = list->head; block != NULL; block = block->d.next)
    {
        printf("Block: 0x%p; size: %ld: is in use: %d\n",
               (void*)block, get_size(block), get_alloc(block));
    }
}

/*
 * prints the heap 
 * used for debugging
 */
static void print_heap()
{
   printf("----------Heap----------\n");
   block_t* block = NULL; 
   for (block = (block_t*)heap_start; 
        block != NULL && get_size(block) > 0; 
        block = find_next(block)){
       printf("block: %p; size: %ld: is in use: %d, prevblock in use: %d\n"
              ,block,get_size(block),get_alloc(block), get_prev_alloc(block));
   } 
   printf("------------------------\n");
}

/*
 * adds block to the given free list  
 */
static void add_tofreelist(block_t *block)
{
    //printf("Adding to free list: 0x%p\n", block);
    freelist_t* list = &freelists[get_free_list_type(get_size(block))];

    if (list->head == NULL) {
        list->head = list->tail = block;
        block->d.next = NULL;
        block->d.prev = NULL;
    } else {
        list->tail->d.next = block;
        block->d.prev = list->tail;
        block->d.next = NULL;
        list->tail = block;
    }
    //print_freelists();
}

/*
 * remove block from free list 
 */
static void remove_fromfreelist(block_t *block)
{
    //printf("Removing from free list: 0x%p\n", block);
    //print_freelists(); 
    freelist_t* list = &freelists[get_free_list_type(get_size(block))];
    block_t *nextblock, *prevblock; 
    nextblock = block->d.next; 
    prevblock = block->d.prev;  
    //assign prevblock's next to nextblock 
    if (nextblock != NULL && prevblock != NULL)
    {
       prevblock->d.next = nextblock;
       nextblock->d.prev = prevblock; 
    }
    else if (prevblock == NULL && nextblock != NULL)
    {  
       // block is the first node
       list->head = nextblock;
       nextblock->d.prev = NULL;
    }
    else if (nextblock == NULL && prevblock != NULL) 
    {
       // block is last node in list
       list->tail = prevblock;
       prevblock->d.next = NULL;
    }
    else
    {
       list->head = list->tail = NULL; 
    }
    block->d.next = NULL; 
    block->d.prev = NULL; 
    //print_freelists();
}

/*
 * combines adjacent free blocks
 */
static block_t *coalesce(block_t * block) 
{
#ifdef ENABLE_PRINT_HEAP
    print_heap();
#endif
    block_t *nextblock = find_next(block);
    // bool next_alloc = get_alloc(nextblock); 
    bool prev_alloc = get_prev_alloc(block);
    block_t *prevblock = prev_alloc ?  NULL : find_prev(block);

    // Case 2, next block is free
    if (nextblock != NULL && nextblock != block  && !get_alloc(nextblock))
    {
       size_t size = get_size(block); 
       //remove the next block from free list
       remove_fromfreelist(nextblock);
       size += get_size(nextblock); 
       // preserve the prev-alloc on current block
       write_header(block, size, false, get_prev_alloc(block));
       write_footer(block, size, false); 
       block_t *nextnextblock = find_next(nextblock);
       if (nextnextblock != NULL) 
       {
            set_prev_alloc(nextnextblock, false);
       } 
    } 
    //Case 3, prev block is free
    if (!prev_alloc && prevblock != NULL && prevblock != block)
    {
       size_t size = get_size(block); 
       size += get_size(prevblock);
       remove_fromfreelist(prevblock); 
       // preserve the prev_alloc for the previous block
       write_header(prevblock, size, false, get_prev_alloc(prevblock));
       write_footer(prevblock, size, false); 

#ifdef ENABLE_PRINT_HEAP
       print_heap(); 
#endif
       return prevblock; 
    }

#ifdef ENABLE_PRINT_HEAP
    print_heap();
#endif
    return block;
}

/*
 * helper function to determine if a block 
 * is used for tinyblocks 
 */
static bool is_min_block(void* bp)
{
   block_t *block = (block_t*) minblocklist.head; 
   while (block != NULL)
   {
        void* start = header_to_payload(block);
        void* end = start + numtinyblocks*tiny_block_size;
        freelist_t *list = (freelist_t *) start; 
        start += tiny_block_size;
        if (bp >= start && bp <= end)
        {
                // printf("is min block\n"); 
                return true; // It is a min block
        }
        block = list->head; 
   }
   return false; 
}

/*
 * fragments block to the right size
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);

    if ((csize - asize) >= min_block_size)
    {
        block_t *block_next;
        write_header(block, asize, true, get_prev_alloc(block));
        // write_footer(block, asize, true);

        block_next = find_next(block);
        //printf("Fragmenting memory. Adding block %p\n", block_next);
        write_header(block_next, csize-asize, false, true);
        // writing this footer because this block is free
        write_footer(block_next, csize-asize, false);

        add_tofreelist(block_next);
    }

    else //block size > min_block_size, allocate entire block
    { 
        write_header(block, csize, true, get_prev_alloc(block));
        set_prev_alloc(find_next(block), true);
        // write_footer(block, csize, true);
    }
}

/*
 * finds block that fits the given size
 * uses memory address to navigate
 */
static block_t *find_fit(size_t asize)
{
    block_t *block;

    for (block = heap_start; get_size(block) > 0;
                             block = find_next(block))
    {

        if (!(get_alloc(block)) && (asize <= get_size(block)))
        {
            return block;
        }
    }
    return NULL; // no fit found
}

/*
 * finds block that fits the given size
 * uses linked list pointers to navigate
 */
static block_t *find_explicitfit(size_t asize)
{
    //printf("Finding explicit fit\n");
    FREELIST_TYPE freelist_type = get_free_list_type(asize); // starting free list
    bool use_best_fit = false;

    while (freelist_type != FREELIST_TYPE_SENTINEL) // iterate through free lists
    {
        block_t *block = NULL;
        block_t* bestfit = NULL;
        freelist_t* list = &freelists[freelist_type];
        for (block = list->head; block != NULL && get_size(block) > 0; block = block->d.next)
        {
            if (!(get_alloc(block)) && (asize <= get_size(block)))
            {
                if (!use_best_fit) {
                   bestfit = block; // return first fit
                   break;
                } else if (!bestfit || get_size(block) < get_size(bestfit)) {
                   bestfit = block; // find best fit
                }
            }
        }
        if (bestfit != NULL) {
            remove_fromfreelist(bestfit);
            //printf("explicit fit returning %p\n", bestfit);
            return bestfit;
        }
        freelist_type += 1; // move to next free list
    }
    //printf("explicit fit returning NULL\n");
    return NULL; // no fit found
}

/* 
 * checks heap for validity of flag bits 
 * found printheap+gdb to be more useful 
 */
bool mm_checkheap(int line)  
{  
   bool result = true; 
   block_t* block = NULL; 
   for (block = (block_t*)heap_start; 
        block != NULL && get_size(block) > 0; 
        block = find_next(block))
   {
        bool isalloc = get_alloc(block); 
        bool isprevalloc = get_prev_alloc(block);
        if (isalloc) 
        {
             block_t *nextblock = find_next(block); 
             if (!get_prev_alloc(nextblock))
             {
                  printf("line: %d - prev alloc NOT set on next block: %p\n", line, nextblock); 
                  result = false; 
             }
        }
        if (isprevalloc)
        {
             block_t *prevblock = find_prev(block); 
             if (!get_alloc(prevblock))
             {
                  printf("line: %d - prev alloc set on block: %p does not match\n", line, block); 
                  result = false; 
             }
        }   
   } 
   return result;
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 *       If the previous block is allocated, the second lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc, bool prev_alloc)
{
    size_t result = prev_alloc ? (size | prev_alloc_mask) : size; 
    return alloc ? (result | alloc_mask) : result;
}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - wsize;
}

static FREELIST_TYPE get_free_list_type(size_t size)
{
    if (size > 16 && size <= 32)
    {
        return FREELIST_TYPE_16_32;
    }
    else if (size > 32 && size <= 64)
    {
        return FREELIST_TYPE_32_64;
    }
    else if (size > 64 && size <= 128)
    {
        return FREELIST_TYPE_64_128;
    }
    else if (size > 128 && size <= 256)
    {
        return FREELIST_TYPE_128_256;
    }
    else if (size > 256 && size <= 512)
    {
        return FREELIST_TYPE_256_512;
    }
    else if (size > 512 && size <= 1024)
    {
        return FREELIST_TYPE_512_1024;
    }
    else if (size > 1024 && size <= 2048)
    {
        return FREELIST_TYPE_1024_2048;
    }
    else if (size > 2048 && size <= 4096)
    {
        return FREELIST_TYPE_2048_4096;
    }
    else if (size > 4096 && size <= 8192)
    {
        return FREELIST_TYPE_4096_8192;
    }
    else if (size > 8192 && size <= 16384)
    {
       return FREELIST_TYPE_8192_16384;
    }
    else 
    {
        return FREELIST_TYPE_REG;
    }
} 

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * extract prev alloc bit from a header
 */
static bool extract_prev_alloc(word_t word)
{
    return (bool)(word & prev_alloc_mask);
}

/*
 * extract min alloc bit from a header
 */
static bool extract_min_alloc(word_t word)
{
    return (bool)(word & min_alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * get_prev_alloc: returns true when prevalloc bit is allocated, false otherwise 
 *
 */
static bool get_prev_alloc(block_t *block)
{
     return extract_prev_alloc(block->header);
}

/*
 * get_min_alloc: returns true when min_alloc bit is set, false otherwise 
 *
 */
static bool get_min_alloc(block_t *block)
{
     return extract_min_alloc(block->header);
}

/*
 * set_prev_alloc: set prev_alloc bit in block 
 * the prev_alloc bit tells if the previous block is allocated
 *
 */
static void set_prev_alloc(block_t *block, bool flag)
{    
     //set prev alloc
     if (flag)
     {
          block->header |= prev_alloc_mask; 
     }
     else 
     {
          block->header &= ~prev_alloc_mask; 
     }
} 

/*
 * set_min_alloc: set min_alloc bit in block 
 * the min_alloc bit tells if the block is allocated minimum_block sizes
 *
 */
static void set_min_alloc(block_t *block, bool flag)
{    
     //set min alloc
     if (flag)
     {
          block->header |= min_alloc_mask; 
     }
     else 
     {
          block->header &= ~min_alloc_mask; 
     }
} 

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc, bool prev_alloc)
{
    block->header = pack(size, alloc, prev_alloc);
    
   // if (alloc) 
   // {   
   //     //if alloc, set prev_alloc of next block 
   //     find_next(block)->header |= prev_alloc_mask; 
   // }
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, alloc, false);
}


/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}
