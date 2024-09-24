# Principles and Practice in Programming Languages

# Lab 2

# Basic Values, Variables, and Judgments

This repository contains the student project files. If you are an instructor looking to re-use these materials, please contact [Bor-Yuh Evan Chang](https://plv.colorado.edu/bec).

Refer to the [lab handout](variables-values-lab.ipynb) in this repository for details about the assignment. The current version of the lab handout is available on the web [here](https://csci3155.cs.colorado.edu/pppl-course/book/variables-values-lab.html).

This file provides some information to help you get started with setting up your development environment.

## Integrity of the Course Materials

The development effort in the course materials, including these lab assignments, the exercises, and the exams, is significant. You agree that you will not share any course materials publicly. The course materials, include your or anyone else's solutions to the lab assignments, exercises, and exams. In particular, you agree not to post your solutions to the lab assignments in a public source code repository, such as public Github repositories. Please use private source code repositories for your work.

## Project Files Organization

For Lab 2, the most important project files are shown below.

```
.
├── README.md (this file)
├── variables-values-lab.ipynb            (the lab handout as a Jupyter Notebook)
└── src
    ├── main
    │   └── scala
    │       └── jsy
    │           └── lab2
    │               ├── Lab2.scala        (implementation template for you to **edit and submit**)
    │               ├── Lab2.worksheet.js (a scratch worksheet you can use to experiment with JavaScript)
    │               ├── Lab2.worksheet.sc (a scratch worksheet you can use to experiment with your code)
    │               ├── Parser.scala      (a parser provided for you)
    │               └── ast.scala         (the AST definition)
    └── test
        └── scala
            └── jsy
                └── lab2
                    └── Lab2Spec.scala    (test cases you can use to test your implementation)

```

## Building and Testing

See [pppl-lab1](https://github.com/csci3155/pppl-lab1) for instructions on building and testing.