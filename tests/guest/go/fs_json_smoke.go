package main

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
)

type record struct {
	ID    int    `json:"id"`
	Name  string `json:"name"`
	Value int    `json:"value"`
}

func main() {
	root, err := os.MkdirTemp("/tmp", "go-fs-json-smoke.")
	if err != nil {
		panic(err)
	}
	defer os.RemoveAll(root)

	records := make([]record, 0, 1024)
	sum := 0
	for i := 0; i < 1024; i++ {
		v := (i*41 + 7) % 1009
		records = append(records, record{
			ID:    i,
			Name:  fmt.Sprintf("item-%04d", i),
			Value: v,
		})
		sum += v
	}

	data, err := json.Marshal(records)
	if err != nil {
		panic(err)
	}

	path := filepath.Join(root, "records.json")
	if err := os.WriteFile(path, data, 0o644); err != nil {
		panic(err)
	}

	readBack, err := os.ReadFile(path)
	if err != nil {
		panic(err)
	}

	var decoded []record
	if err := json.Unmarshal(readBack, &decoded); err != nil {
		panic(err)
	}

	if len(decoded) != len(records) {
		panic(fmt.Sprintf("decoded len mismatch: %d != %d", len(decoded), len(records)))
	}

	checksum := 0
	for _, rec := range decoded {
		checksum += rec.Value
	}

	if checksum != sum {
		panic(fmt.Sprintf("checksum mismatch: %d != %d", checksum, sum))
	}

	fmt.Printf("go_fs_json_smoke ok records=%d checksum=%d bytes=%d\n", len(decoded), checksum, len(readBack))
}
