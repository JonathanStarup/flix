| problem                           | paper         | scala2            | scala3            | flix              |
| --------------------------------- | ---           | ---               | ---------         | ---               |
| Type of compileExp                | GADT          | GADT              | GADT              |                   |
| op stack modelling                | type stack    | type stack        | type stack        | record type stack |
| Composite value (fixed length)    | ???           | indexed PType     | indexed PType     | ???               |
| Composite value (variable length) | h-list(?)scala|                   |                   |                   |
| Cat1/2                            | implicit class| implicit class    | implicit class    | type class        |
| undetermined inner exp types      | _ <: PType    | _ <: PType        | _ <: PType        | ???               |
| branching instructions            | ???           | RType & GADT      | Rtype & GADT      | ???               |
| using JVM classes                 | ???           | model in code     | model in code     | model in code     |
| objects/putfield/getfield         | ???           | model in code     | model in code     | ???               |
| local stack                       | capability    | ???               | ???               | stack in record   |
| string creation                   | ???           | type/str builder  | type/str builder  | ???               |
| list of expressions (ex. tuple)   | ???           | List on stack     | List on stack     | List on stack     |
| branching code                    | ???           | capability        | capability        | ???               |
| lock on this                      | ???           | capability        | capability        | boolean on record |
| exception handling                | ???           | ???               | ???               | boolean on record |
| casting/erasure                   | ???           | hidden in model   | hidden in model   | ???               |
| inference                         | trials & hints| trials & hints    | trials & hints    | complete          |
| adding static knowledge           | extra F syntax| extra F syntax    | extra F syntax    | record ... syntax |


* stack underflow
* stack overflow ("unpopped values", fine in jvm)
* operand and operator stacks match
* read/write existing locals (visitmaxs)
* type safe local read/write
* classes/fields/methods names/types
* cat1/2
* jump maintain stack
* locking / unlocking
* exception throw/catch

classify verify error vs. invariants in flix vs. suspicious


# Plan

30 jun: paper draft, 2col, min. 6-8 pages (toy lang + diff) (exploring design space)
15 aug: code done, all test pass, performance inside x1.2
31 aug: project deadline (formal deadline)
31 aug: al code merged in, reviewed, etc.
 1 sep: nyt project (stratified negation / Provenance)
 1 sep onwards: backend text writing
   oct: paper submit
