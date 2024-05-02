const importObject = {};
WebAssembly.instantiateStreaming(fetch("subkernel.wasm"), importObject).then(
  (kernel) => {
    window.kernel = kernel;
    WebAssembly.instantiateStreaming(fetch("demo2.wasm"), {kernel: kernel.instance.exports}).then(
      (payload) => {
        window.payload = payload;
      }
    );
  }
);

