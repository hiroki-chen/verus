package main

import (
	"fmt"
	"sync"
)

const (
	workerCount = 8
	taskCount   = 10000
)

type result struct {
	id    int
	value uint64
}

func worker(tasks <-chan int, results chan<- result, wg *sync.WaitGroup) {
	defer wg.Done()
	for task := range tasks {
		v := uint64(task)
		acc := uint64(0xcbf29ce484222325)
		for i := 0; i < 64; i++ {
			acc ^= v + uint64(i*17)
			acc *= 0x100000001b3
			acc ^= acc >> 13
		}
		results <- result{id: task, value: acc}
	}
}

func main() {
	tasks := make(chan int, 256)
	results := make(chan result, 256)
	var wg sync.WaitGroup

	for i := 0; i < workerCount; i++ {
		wg.Add(1)
		go worker(tasks, results, &wg)
	}

	go func() {
		for i := 0; i < taskCount; i++ {
			tasks <- i
		}
		close(tasks)
	}()

	go func() {
		wg.Wait()
		close(results)
	}()

	var checksum uint64
	count := 0
	for res := range results {
		checksum ^= uint64(res.id)*0x9e3779b97f4a7c15 + res.value
		count++
	}

	if count != taskCount {
		panic(fmt.Sprintf("result count mismatch: %d != %d", count, taskCount))
	}

	fmt.Printf("go_concurrency_smoke ok workers=%d tasks=%d checksum=%d\n", workerCount, count, checksum)
}
