# nice_tree

A small, simple console program and a library that operates on binary trees of integer numbers. It doesn't make much sense. I've written it just as an exercise to learn Rust programming language. That's my first program in this language.

The program can parse a tree from special syntax, passed on standard input (default), file (`-i` parameter) or directly as parameter (`-d` parameter) and output it in nice ASCII-art form to standard output (default) or file (`-o` parameter). It can also generate a random tree (`-g` parameter). The library contains more internal functionality, like iterator for traversing the tree preorder, inorder, and postorder.

Example command line usage:

```
> nice_tree -d "(1 (-2 21 22) (3 _ (32)))"
1
├── -2
│   ├── 21
│   └── 22
└── 3
    ├── _
    └── 32
```

Any feedback is welcomed, especially regarding my usage of idiomatic Rust.
