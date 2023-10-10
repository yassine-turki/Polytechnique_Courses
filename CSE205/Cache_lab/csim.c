#include <getopt.h>
#include <stdio.h>
#include <stdlib.h>

#include "cachelab.h"

//Name = Yassine Turki
//User Id = yassine.turki

/* Globals set by command line args */
int verbosity = 0; /* print trace if set */
int s = 0;         /* set index bits */
int b = 0;         /* block offset bits */
int E = 0;         /* associativity */
char* trace_file = NULL;

/*
 * printUsage - Print usage info
 */
void printUsage(char* argv[])
{
    printf("Usage: %s [-hv] -s <num> -E <num> -b <num> -t <file>\n", argv[0]);
    printf("Options:\n");
    printf("  -h         Print this help message.\n");
    printf("  -v         Optional verbose flag.\n");
    printf("  -s <num>   Number of set index bits.\n");
    printf("  -E <num>   Number of lines per set.\n");
    printf("  -b <num>   Number of block offset bits.\n");
    printf("  -t <file>  Trace file.\n");
    printf("\nExamples:\n");
    printf("  linux>  %s -s 4 -E 1 -b 4 -t traces/yi.trace\n", argv[0]);
    printf("  linux>  %s -v -s 8 -E 2 -b 4 -t traces/yi.trace\n", argv[0]);
    exit(0);
}


typedef struct{
  int valid;
  unsigned long tag;
  int usage_order; //usage_order in which the line was used
} line_t;

typedef line_t *set_t;
typedef set_t *cache_t;


/*
 * main - Main routine 
 */
int main(int argc, char* argv[])
{
  char c;
  
  while( (c=getopt(argc,argv,"s:E:b:t:vh")) != -1){
    switch(c){
    case 's':
      s = atoi(optarg);
      break;
    case 'E':
      E = atoi(optarg);
      break;
    case 'b':
      b = atoi(optarg);
      break;
    case 't':
      trace_file = optarg;
      break;
    case 'v':
      verbosity = 1;
      break;
    case 'h':
      printUsage(argv);
      exit(0);
    default:
      printUsage(argv);
      exit(1);
    }
  }

  /* Make sure that all required command line args were specified */
  if (s == 0 || E == 0 || b == 0 || trace_file == NULL) {
    printf("%s: Missing required command line argument\n", argv[0]);
    printUsage(argv);
    exit(1);
  }

  int sets=1<<s; //Number of sets
  int hits=0;
  int misses=0;
  int evictions=0;

  char operation; // "S" for store, "L" for load, "M" for modify 
  unsigned long address;
  int size;
  int cache_usage_order = 0; //usage_order in which the cache was used

// Read file
  FILE *file;
  file = fopen(trace_file, "r");
  if (file == NULL)
  {
    printf("Cannot open trace file");
    exit(1);
  }

// initialize the cache
cache_t cache = (cache_t)malloc(sets*sizeof(set_t));
  for(int i=0;i<sets;i++){
    cache[i]=(set_t)malloc(E*sizeof(line_t));
    for(int j=0;j<E;j++){
      cache[i][j].valid=0;
      cache[i][j].tag=0;
      cache[i][j].usage_order=0;
    }
  } 


  // Cache simulation
  while (fscanf(file, " %c %lx,%d", &operation, &address, &size) == 3)
    {

        if (operation == 'I')
        { // Ignore instruction load
            continue;
        }

      //Get the set index and tag
        int set_index = (address >> b) & ((sets) - 1);
        unsigned long tag = address >> (s + b);

        int hit = 0;
        int empty_line = -1; //index of the empty line
        int min_usage_order = cache[set_index][0].usage_order; //min_usage_order in which the line was used
        int min_usage_order_index = 0; //index of the line with the min_usage_order

        for (int i = 0; i < E; i++)
        {
            if (cache[set_index][i].valid == 1) //valid line
            {
                if (cache[set_index][i].tag == tag) //tag match
                {
                    hit = 1; //We have a hit
                    cache[set_index][i].usage_order = cache_usage_order++; //update the usage_order
                    break;
                }
                if (cache[set_index][i].usage_order < min_usage_order) //update the min_usage_order
                {
                    min_usage_order = cache[set_index][i].usage_order;
                    min_usage_order_index = i;
                }
            }
            else
            {
                empty_line = i; //We have an empty line
            }
        }

        if (hit == 0) //We have a miss
        {
            if (empty_line != -1) //We have an empty line
            {
                cache[set_index][empty_line].valid = 1;
                cache[set_index][empty_line].tag = tag;
                cache[set_index][empty_line].usage_order = cache_usage_order++; 
            }
            else
            { //We have an eviction
                evictions++;
                cache[set_index][min_usage_order_index].tag = tag;
                cache[set_index][min_usage_order_index].usage_order = cache_usage_order++;
            }
        }

        if (operation == 'L' )
        {
            if (hit == 1)
            {
                hits++;
            }
            else
            {
                misses++;
            }
        }
        else if (operation == 'S')
        {
            if (hit == 1)
            {
                hits++;
            }
            else
            {
                misses++;
            }
        }
        else if (operation == 'M')
        {
            if (hit == 1)
            {
                hits++;
            }
            else
            {
                misses++;
            }
            hits++;
        }
    }

    // We free the cache and close the file
    for (int i = 0; i < sets; i++)
    {
        free(cache[i]);
    }
    free(cache);

    fclose(file);

    printSummary(hits, misses, evictions);
    return 0;
}