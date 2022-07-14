# Eazy Functional Language (Interpreter)

### The language supports i.a. 

+ partial application and higher order functions
+ algebraic polymorphic data types with recursion
+ nested pattern matching
+ warnings about incomplete pattern matching
+ type inference algorithm
+ complete static typing


### Syntax 
All constructions in the Eazy Language are typical and do not require elaboration. Examples can be found in the `examples` direcotry.

* Infix arithmetic operators: `+, -, *, /`
* Infix logical operators: `&&, ||, ==, =/=, <, >, <=, >=`
* Arithmetic negation: `-`
* Logical negation: `~`
* "IF" clause: `(wyrażenie) if (warunek) otherwise (wyrażenie)`
* "MATCH" construction: `match (wyrażenie) with { (wzorzec -> wyrażenie)+ }`
    * Match naming convention:  `wzorzec as id`
* "LET" construction: `let { (deklaracje) } in (wyrażenie)`
* Anonymous functions: `lambda{ (typ) } (parametry) -> (wyrażenie)`
* Lists constructions: `[ (wyrażenia) ], głowa :: ogon`
* Function type declarations: `(nazwa) : (typ)`
* Creating new times: `type (Nazwa) (parametry) = (Opcja1) (parametry) | (Opcja2) (parametry) | ...`
* Comments: `;) (treść) (;, ;* (treść)`


### Grammar 

The syntax parser was generated using the [BNF converter](https://bnfc.digitalgrammars.com/).
The grammar can be found in the file `eazy.cf`.

### Running

After aquiring the `bnfc` execuatble, set the `BNFC_PATH` in the `Makefile` accordingly.
Afterwards run `make` in the directory with source files. Then the interpreter can be run in 2 ways:  
1: Reading from stdin until `^D`
```
./interpreter 
```
2: Reading from a file
```
./interpreter path_to_file.ez
```
