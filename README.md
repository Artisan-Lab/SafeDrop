# SafeDrop

### NOTE!!!The project is obsolete!!! We have integrated the features of SafeDrop into [RAP](https://github.com/Artisan-Lab/RAP).

A additional Rust compiler pass to detect memory safe bugs of Rust programs. SafeDrop performs path-sensitive and field-sensitive inter-procedural static analysis based on the mid-level IR of Rust program. It uses the tarjan algorithm to deal with the complex control flow loop and function call loop,
then performs alias analysis on each execution path, detecting potential problems and reporting errors depend on our summarized rules.

The associated paper titled *SafeDrop: Detecting Memory Deallocation Bugs of Rust Programs via Static Data-Flow Analysis* (TOSEM '22).



## Requirement

- First, git clone the Rust compiler source code.

  ```
  $ git clone https://github.com/rust-lang/rust.git
  ```

  Since this implementation is based on Rust  `1.63.0`, it need to switch to the corresponding tag.

  ```shell
  $ cd rust
  $ git checkout -b mycompiler 1.63.0
  ```

- Make sure you can build the Rust compiler. The specific requirements and tutorial you can find in https://github.com/rust-lang/rust.



## Usage

It need to add some code snippets to make this pass work.

- Modify the compiler source code according to the `need_to_modify.rs` and `lib.rs`.

- put the `safedrop_check` module under the `rust/compiler/rustc_mir_transform/`

  - rebuild the compiler,  and we can get the compiler with safedrop checking: `rust/build/(target_machine)/stage1/bin/rustc`.

- You can set this compiler in rust toolchain use:

  ```shell
  # link this compiler as safedrop in rust toolchains.
  $ rustup toolchain link safedrop path_to_rust/build/(target_machine)/stage1
  # set the default toolchain as safedrop.
  $ rustup default safedrop
  ```

  After that, you can use both `rustc` or `cargo` to compile rust programs with safedrop checking.

- example:

  ```rust
  // a program with double-free bug
  use std::vec::Vec;
  fn main() {
      let mut a = vec![1,2];
      let ptr = a.as_mut_ptr();
      unsafe{
          let mut _v = Vec::from_raw_parts(ptr, 2, 2);
      }
  }
  ```

  We use this compiler to compile this program, and can get the following warning message:

  ```shell
  $ rustc test.rs
  =================================
  Function:DefId(0:6 ~ test[5105]::main)
  Double Free Bugs Exist:
  occurs in test.rs:9:1: 9:2 (#0)
  
  ```
