#define _POSIX_C_SOURCE 199309L

#include <assert.h>
#include <inttypes.h>
#include <limits.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>

// #include <rte_eal.h>
// #include <rte_lcore.h>
// #include <rte_memzone.h>

#include <x86intrin.h>

#define PAGE_SIZE (1 << 22)
#define ARRAY_SIZE (1ul * PAGE_SIZE)
// #define ASSOCIATIVITY 20
// #define DELAY_THRESHOLD 80
#define DELAY_DELTA_THRESHOLD 300
#define OFFSET_BITS 15
#define LOOP_REPETITIONS 10000000
#define PROBE_TRIALS 10

uint64_t timestamp;

char *array;

static inline void start() {
  timestamp = __rdtsc();
}

static inline uint64_t stop() {
  uint64_t new_timestamp = __rdtsc();

  return new_timestamp - timestamp;
}

int is_empty(long entry) { return entry < 0; }

long get_size(long entry) {
  if (entry < 0) {
    return 0;
  }

  if (*((long *)&array[entry]) == entry) {
    return 1;
  }

  long pos = entry, size = 0;
  do {
    pos = *((long *)&array[pos]);
    size++;
  } while (pos != entry);

  return size;
}

void insert(long *pos, long item) {
  assert(item >= 0);
  assert(*((long *)&array[item]) == item);

  if (*pos < 0) {
    *pos = item;
  }

  if (*pos != item) {
    *((long *)&array[item]) = *((long *)&array[*pos]);
    *((long *)&array[*pos]) = item;
  }
}

long drop_next(long *entry, long pos) {
  assert(*entry >= 0);
  assert(pos >= 0);

  long drop = *((long *)&array[pos]);

  if (drop == *entry) {
    if (pos == *entry) {
      *entry = -1;
    } else {
      *entry = pos;
    }
  }

  *((long *)&array[pos]) = *((long *)&array[drop]);
  *((long *)&array[drop]) = drop;

  return drop;
}

void swap(long pos1, long pos2) {
  assert(pos1 >= 0 && pos2 >= 0);

  long pos1s = *((long *)&array[pos1]);
  long pos1ss = *((long *)&array[pos1s]);
  long pos2s = *((long *)&array[pos2]);
  long pos2ss = *((long *)&array[pos2s]);

  if (pos1 == pos2s) {
    *((long *)&array[pos1]) = pos1ss;
    *((long *)&array[pos1s]) = pos2s;
  } else {
    *((long *)&array[pos1]) = pos2s;
    *((long *)&array[pos1s]) = pos2ss;
  }
  if (pos2 == pos1s) {
    *((long *)&array[pos2]) = pos2ss;
    *((long *)&array[pos2s]) = pos1s;
  } else {
    *((long *)&array[pos2]) = pos1s;
    *((long *)&array[pos2s]) = pos1ss;
  }
}

void shuffle(long entry) {
  assert(entry >= 0);

  long pre_size = get_size(entry);

  long size = pre_size, pos = entry;
  if (size > 2) {
    do {
      long swap_count = rand() / (RAND_MAX / size + 1),
           swap_pos = *((long *)&array[pos]);
      if (swap_count > 0) {
        while (swap_count-- > 0) {
          swap_pos = *((long *)&array[swap_pos]);
        }

        swap(pos, swap_pos);
      }

      size--;
      pos = *((long *)&array[pos]);
    } while (size > 0);
  }

  assert(get_size(entry) == pre_size);
}

uint64_t probe(long entry) {
  if (entry < 0) {
    return 0;
  }

  long idx = entry;

  // Prime.
  do {
    idx = *((long *)&array[idx]);
  } while (idx != entry);

  // Probe.
  start();
  for (size_t i = 0; i < LOOP_REPETITIONS; i++) {
    do {
      idx = *((long *)&array[idx]);
    } while (idx != entry);
  }
  uint64_t delay = stop();

  return delay / LOOP_REPETITIONS;
}

uint64_t min_probe(long entry) {
  uint64_t min = probe(entry);
  for (int i = 1; i < PROBE_TRIALS; i++) {
    uint64_t p = probe(entry);
    if (p < min) {
      min = p;
    }
  }
  return min;
}

int main(int argc, char *argv[]) {
  // Initialize the Environment Abstraction Layer (EAL)
  // int ret = rte_eal_init(argc, argv);
  // if (ret < 0) {
  //   rte_exit(EXIT_FAILURE, "Error with EAL initialization, ret=%d\n", ret);
  // }
  // argc -= ret;
  // argv += ret;

  // assert(argc == 2 && "Usage: probe-slices <set-file>");
  // FILE *file = fopen(argv[1], "w");
  // assert(file && "Unable to open set file.");

  // printf("Exploring array of %ld bytes, %ld lines.\n", ARRAY_SIZE,
  //        ARRAY_SIZE >> OFFSET_BITS);
  // printf("Writing contention sets to: %s.\n", argv[1]);

  // const struct rte_memzone *mz = rte_memzone_reserve_aligned(
  //     "Array", ARRAY_SIZE, rte_socket_id(), RTE_MEMZONE_1GB, PAGE_SIZE);

  // assert(mz && "Unable to allocate memory zone.");
  char *orig_array = malloc(ARRAY_SIZE + 64);
  assert(orig_array != NULL);
  // Align to 64 bytes
  array = (char *)(((uintptr_t)orig_array + 64) & 0xFFFFFFFFFFFFFFC0);

  // printf("Array physical address: %016lX\n", rte_mem_virt2phy(array));

  // Spot check if page is actually 1GB.
  // assert(rte_mem_virt2phy(array + (1 << 30) - 1) - rte_mem_virt2phy(array) ==
  //            (1 << 30) - 1 &&
  //        "Physical page is not a 1GB contiguous block.");

  srand(0);

  // Init line sets.
  long running_set = -1, remaining_set = 0;
  *((long *)&array[remaining_set]) = remaining_set;
  for (long i = 1; (i << OFFSET_BITS) < ARRAY_SIZE; i++) {
    *((long *)&array[i << OFFSET_BITS]) = i << OFFSET_BITS;
    insert(&remaining_set, i << OFFSET_BITS);
  }
  shuffle(remaining_set);

  printf("%" PRIu64 "\n", probe(0));

  free(orig_array);

/*  // Warm-up
  min_probe(remaining_set);

  int contention_set_id = 0;
  do {
    printf("Learning contention set %d.\n", contention_set_id);
    printf("%ld lines remaining.\n", get_size(remaining_set));
    printf("Growing contention set.\n");
    uint64_t delay = 0, prev_delay;
    do {
      if (get_size(remaining_set) == 0) {
        break;
      }
      insert(&running_set, drop_next(&remaining_set, remaining_set));

      prev_delay = delay;
      delay = min_probe(running_set);
      //       printf("Contention set of %d blocks had delay of %d (delta =
      //       %d).\n",
      //              get_size(running_set), delay, delay - prev_delay);
    } while (delay - prev_delay <= DELAY_DELTA_THRESHOLD);
    //     printf("%d lines remaining.\n", get_size(remaining_set));

    printf("Shrinking contention set.\n");
    long pos = running_set;
    uint64_t pre_delay = min_probe(pos);
    uint64_t found;
    do {
      found = 0;

      if (is_empty(running_set)) {
        break;
      }

      int done;
      do {
        //         printf("Contention set of %d blocks had delay of %d.\n",
        //               get_size(running_set), pre_delay);

        done = *((long *)&array[pos]) == running_set;
        long dropped = drop_next(&running_set, pos);
        uint64_t post_delay = min_probe(running_set);

        //         printf("Contention set of %d blocks had delay of %d (delta =
        //         %d).\n",
        //                get_size(running_set), post_delay, post_delay -
        //                pre_delay);

        if ((post_delay - pre_delay) < -DELAY_DELTA_THRESHOLD) {
          // Big drop: address is in contention set. Put it back.
          insert(&pos, dropped);
        } else if (post_delay > pre_delay) {
          // Increase: measurement is broken. Redo.
          insert(&pos, dropped);
          pre_delay = min_probe(pos);
          continue;
        } else {
          // Small drop: address is not in contention set. Leave it out.
          insert(&remaining_set, dropped);
          pre_delay = post_delay;
          found = 1;
        }

        pos = *((long *)&array[pos]);
      } while (!done);
    } while (found);

    if (is_empty(running_set)) {
      printf("Contention set %d didn't hold up. Retrying.\n",
             contention_set_id);
      continue;
    }

    printf("Contention set %d has %ld ways.\n", contention_set_id,
           get_size(running_set) - 1);
    // fprintf(file, "%ld\n", get_size(running_set) - 1);

    //     printf("%d lines remaining.\n", get_size(remaining_set));
    printf("Finding further lines.\n");
    // Drop a line from the running set but keep it as the contention set.
    long contention_set = drop_next(&running_set, running_set), tested_set = -1;
    while (get_size(remaining_set)) {
      uint64_t pre_delay = min_probe(running_set);
      //       printf("Contention set of %d blocks had delay of %d.\n",
      //             get_size(running_set), pre_delay);

      long candidate = drop_next(&remaining_set, remaining_set);
      insert(&running_set, candidate);

      uint64_t post_delay = min_probe(running_set);

      //       printf("Contention set of %d blocks had delay of %d (delta =
      //       %d).\n",
      //              get_size(running_set), post_delay, post_delay -
      //              pre_delay);

      if (post_delay - pre_delay > DELAY_DELTA_THRESHOLD) {
        insert(&contention_set, drop_next(&running_set, running_set));
      } else {
        insert(&tested_set, drop_next(&running_set, running_set));
      }
      //       printf("%d lines remaining.\n", get_size(remaining_set));
    }
    remaining_set = tested_set;

    // Merge running set with contention set.
    while (get_size(running_set)) {
      insert(&contention_set, drop_next(&running_set, running_set));
    }

    printf("Contention set %d has %ld elements.\n", contention_set_id++,
           get_size(contention_set));
    // while (get_size(contention_set)) {
    //   fprintf(file, "%ld\n", drop_next(&contention_set, contention_set));
    // }
    // fprintf(file, "\n");
  } while (remaining_set >= 0);
  printf("Found %d contention sets.\n", contention_set_id++);
  // fclose(file);
*/
  return 0;
}
