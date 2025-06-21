Fun is a new programming language.

Specifications: 

https://github.com/paraguayrussianblue/fun-parser/blob/main/README.md

Type System of Fun Language:

Type Structure Fun has the types of integer, n-ary tuples, single-argument/single-return function and reference.

tp ::= int | <tp, ..., tp> | tp -> tp | tp ref | (tp)

The name “int” is not a reserved word, it is an ordinary identifier. 

The ref constructor has higher precedence (binds tighter) than the function type constructor (->). 

The function type constructor is right associative and the ref type constructor is left associative.

Typing Rules:

The judgment Γ ⊢ exp : tp states that expression exp has type tp in Γ. A context (or environment) Γ contains mappings from identifiers to types.

<img width="830" alt="스크린샷 2025-06-22 오전 12 02 45" src="https://github.com/user-attachments/assets/228dde03-5a40-45c5-8d3a-17b21c8868dc" />

<img width="830" alt="스크린샷 2025-06-22 오전 12 06 52" src="https://github.com/user-attachments/assets/9256acd1-d954-4818-b7db-c752a1f5cefe" />

The optype function, which returns the type of an operator, is defined by the following table:

<img width="627" alt="스크린샷 2025-06-22 오전 12 08 05" src="https://github.com/user-attachments/assets/8804ba77-483a-4f2f-9589-4ea7e6521273" />

✱ The last rule related to subtyping is called the subsumption rule, which works implicitly for the other rules. That is, you have to consider the subsumption rule when you implement the other rules. Let’s consider if 10 then < 1 > else < 1, 2 >. Should typing fail with the expression?

File Infos:

• lib/typecheck.ml: code for type checking

• lib/absyn.ml: abstract syntax tree definition

• lib/symbol.ml: symbol table definition

• lib/errormsg.ml, errormsg.mli: code for printing error message • lib/funpar.ml, funpar.mli: parser for the Fun language

• lib/funlex.ml: lexical analyzer for the Fun language

• data/*.fun : test programs in the Fun language

