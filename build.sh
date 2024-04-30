wasm-tools parse kernel.wat -o kernel.wasm && wasm-tools validate --features all kernel.wasm
wasm-tools parse demo0.wat -o demo0.wasm && wasm-tools validate --features all demo0.wasm
python3 -m http.server
