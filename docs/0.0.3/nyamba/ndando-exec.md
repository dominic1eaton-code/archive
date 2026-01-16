# NDANDO EXECUTION AND COMPUTATIONAL MODELS
## Technical Specification Document v1.0

**Status:** Canonical  
**Version:** 1.0  
**Date:** 2025-01-16  
**Authors:** Ndando Language Design Committee  

---

## TABLE OF CONTENTS

1. [Introduction](#1-introduction)
2. [Ndando-A: Assembly Language Execution Model](#2-ndando-a-assembly-language-execution-model)
3. [Ndando-C: Compiled Language Execution Model](#3-ndando-c-compiled-language-execution-model)
4. [Ndando-P: Interpreted Language Execution Model](#4-ndando-p-interpreted-language-execution-model)
5. [Cross-Layer Execution Semantics](#5-cross-layer-execution-semantics)
6. [Implementation Guidelines](#6-implementation-guidelines)

---

## 1. INTRODUCTION

This document specifies the formal execution and computational models for the three-tier Ndando language family: Ndando-A (Assembly), Ndando-C (Compiled), and Ndando-P (Pythonic Interpreted).

### 1.1 Language Hierarchy

```
Ndando-P (Intent/Policy Layer)
    ↓ interpret + desugar
Ndando-C (Structural/Typed Layer)
    ↓ compile
Ndando-A (Canonical/Assembly Layer)
    ↓ execute
CivOS Kernel Runtime
```

### 1.2 Design Principles

- **Determinism:** All execution is deterministic and reproducible
- **Auditability:** All effects are logged to the Songhai Evolution Ledger (SEL)
- **Safety:** Type safety and memory safety at all layers
- **Transparency:** All operations are explicit; no hidden control flow

---

## 2. NDANDO-A: ASSEMBLY LANGUAGE EXECUTION MODEL

### 2.1 Abstract Machine Definition

**Ndando-A Abstract Machine (NAAM)**

```
NAAM = (Q, Σ, Γ, δ, q₀, F)

Where:
  Q  = {executing, waiting, repairing, collapsed, terminated}
  Σ  = Instruction alphabet (operators + operands)
  Γ  = Memory tape alphabet (values + types)
  δ  = Transition function (state × instruction → state × effect)
  q₀ = executing (initial state)
  F  = {terminated} (accepting states)
```

### 2.2 Machine Components

**Memory Architecture:**
```
Memory = {
  Registers:   R[0..15]      // General purpose registers
  Stack:       S[0..1023]    // Execution stack (LIFO)
  Ledger:      L[0..∞]       // Append-only audit log
  Canon:       C[0..∞]       // Immutable once written
  Heap:        H[0..∞]       // Dynamic allocation
}
```

**Register Set:**
```
R0-R7:   General purpose
R8-R11:  Temporary (caller-saved)
R12-R13: Frame pointer, stack pointer
R14:     Link register (return address)
R15:     Program counter (instruction pointer)
```

### 2.3 Instruction Execution Cycle

**Seven-Phase Cycle:**

```
1. FETCH:    PC → IR (instruction register)
             Load instruction from code segment

2. DECODE:   IR → opcode, operands
             Parse instruction format

3. VALIDATE: type_check(operands)
             Verify type constraints and arity

4. EXECUTE:  perform operation
             Modify machine state

5. LOG:      append to ledger
             Record operation in SEL

6. UPDATE:   PC++, update state
             Advance program counter

7. CHECK:    collision detection, repair needed?
             Verify invariants
```

**Cycle Pseudocode:**
```python
def execution_cycle(machine, instruction):
    # FETCH
    ir = machine.memory[machine.pc]
    
    # DECODE
    opcode, operands = decode(ir)
    
    # VALIDATE
    if not validate_types(opcode, operands):
        raise TypeError(f"Invalid operands for {opcode}")
    
    # EXECUTE
    result = execute_operator(opcode, operands, machine)
    
    # LOG
    machine.ledger.append({
        'pc': machine.pc,
        'op': opcode,
        'args': operands,
        'result': result,
        'timestamp': now()
    })
    
    # UPDATE
    machine.pc += 1
    machine.state = compute_next_state(machine)
    
    # CHECK
    verify_invariants(machine)
    
    return machine
```

### 2.4 Operational Semantics (Small-Step)

**Configuration:**
```
⟨I, M, L⟩
  I = Instruction sequence (list)
  M = Memory state (map)
  L = Ledger state (append-only list)
```

**Transition Rules:**

**[GROW]**
```
⟨x ^ y :: I, M, L⟩ → ⟨I, M[x ↦ y], L⟩   
  where x ⊆ y (x is contained in y)
```

**[SPAWN]**
```
⟨x >> y :: I, M, L⟩ → ⟨I, M[y ↦ new(type(x))], L ∪ {spawn(y)}⟩
```

**[BOOT]**
```
⟨project ! :: I, M, L⟩ → ⟨I, M[kernel ↦ loaded], L ∪ {boot}⟩
```

**[RUN]**
```
⟨program ~ :: I, M, L⟩ → ⟨I, M[cycle ↦ active], L ∪ {run}⟩
```

**[CYCLE]**
```
⟨cycle @ :: I, M, L⟩ → ⟨I, M[process ↦ spawned], L ∪ {cycle}⟩
```

**[COLLAPSE]**
```
⟨X e :: I, M, L⟩ → ⟨I, M[e ↦ failure], L ∪ {collapse(e)}⟩
```

**[REPAIR]**
```
⟨~> f :: I, M, L⟩ → ⟨I, M[f ↦ repaired(f)], L ∪ {repair(f)}⟩
  where f : Failure ∧ repairable(f)
```

**[ADAPT]**
```
⟨~~> f :: I, M, L⟩ → ⟨I, M[f ↦ adapted(f)], L ∪ {adapt(f)}⟩
  where f : Failure ∧ ¬repairable(f)
```

**[MYCORRHIZATE]**
```
⟨x <> y :: I, M, L⟩ → ⟨I, M[link(x,y)], L ∪ {couple(x,y)}⟩
  where x : Forest ∧ y : Forest
```

**[CANONIZE]**
```
⟨## e :: I, M, L⟩ → ⟨I, M, L ∪ {canon(e)}⟩
  where e promoted to Canon (immutable)
```

**[HALT]**
```
⟨stop :: I, M, L⟩ → ⟨[], M, L⟩
```

### 2.5 Type System

**Base Types:**
```
τ ::= Kernel | Project | Program | Cycle | Process
    | String | Seed | Tree | Forest
    | Failure | Decision
    | τ → τ (function types, not user-definable)
```

**Typing Rules:**

**[T-BOOT]**
```
Γ ⊢ p : Project
─────────────────
Γ ⊢ !p : Program
```

**[T-SPAWN]**
```
Γ ⊢ x : String
─────────────────
Γ ⊢ x >> seed : Seed
```

**[T-GROW]**
```
Γ ⊢ s : Seed
─────────────────
Γ ⊢ s ^ tree : Tree
```

**[T-COLLAPSE]**
```
Γ ⊢ e : τ
─────────────────
Γ ⊢ X e : Failure
```

**[T-REPAIR]**
```
Γ ⊢ f : Failure
─────────────────
Γ ⊢ ~> f : τ
```

**[T-MYCOR]**
```
Γ ⊢ t₁ : Forest   Γ ⊢ t₂ : Forest
──────────────────────────────────
Γ ⊢ t₁ <> t₂ : ForestCoupling
```

### 2.6 Computational Complexity

**Time Complexity:**
- Basic operation: O(1)
- Spawn operation: O(log n) (allocation)
- Repair operation: O(n) worst case (depends on repair grammar)
- Mycorrhizate: O(m + n) for forests of size m and n

**Space Complexity:**
- Stack: O(depth) where depth is recursion depth
- Ledger: O(operations) - grows with program length
- Canon: O(canonized_items)
- Heap: O(live_objects)

### 2.7 Termination Properties

**Non-Termination by Design:**
```
There is no guaranteed terminal state. Execution can:
1. Continue indefinitely (forest >> kernel recursion)
2. Collapse (explicit failure)
3. Repair (recovery from failure)
4. Adapt (transformation after failed repair)
```

**Termination Conditions:**
- Explicit `stop` instruction
- Unrecoverable collapse (no repair grammar available)
- Resource exhaustion (stack overflow, memory)

---

## 3. NDANDO-C: COMPILED LANGUAGE EXECUTION MODEL

### 3.1 Abstract Machine Definition

**Ndando-C Abstract Machine (NCAM)**

```
NCAM = (Code, Stack, Heap, Env, PC)

Where:
  Code = Instruction sequence (bytecode)
  Stack = Evaluation stack
  Heap = Typed object storage
  Env = Environment (variable bindings)
  PC = Program counter
```

### 3.2 Compilation Model

**Compilation Pipeline:**

```
Ndando-C Source
    ↓
[Lexical Analysis]
    ↓
Token Stream
    ↓
[Syntax Analysis]
    ↓
Abstract Syntax Tree (AST)
    ↓
[Type Checking]
    ↓
Typed AST
    ↓
[Optimization]
    ↓
Optimized AST
    ↓
[Code Generation]
    ↓
Ndando-A Instructions
```

### 3.3 Type System (Hindley-Milner Style)

**Type Inference Algorithm W:**

```
infer(Γ, e) = case e of
  x              → lookup(Γ, x)
  
  λx.e           → let τ₁ = fresh()
                       τ₂ = infer(Γ ∪ {x:τ₁}, e)
                   in τ₁ → τ₂
  
  e₁ e₂          → let τ₁ = infer(Γ, e₁)
                       τ₂ = infer(Γ, e₂)
                       τ₃ = fresh()
                       unify(τ₁, τ₂ → τ₃)
                   in τ₃
  
  if e₁ e₂ e₃    → let unify(infer(Γ, e₁), Bool)
                       τ₂ = infer(Γ, e₂)
                       τ₃ = infer(Γ, e₃)
                       unify(τ₂, τ₃)
                   in τ₂
```

**Unification:**
```
unify(τ₁, τ₂) = case (τ₁, τ₂) of
  (α, τ)         → if α ∉ FV(τ) then [α ↦ τ] else fail
  (τ, α)         → unify(α, τ)
  (τ₁ → τ₂, τ₃ → τ₄) → unify(τ₁, τ₃) ∘ unify(τ₂, τ₄)
  (Base₁, Base₂) → if Base₁ = Base₂ then id else fail
```

### 3.4 Big-Step Operational Semantics

**Environment:** `ρ : Var → Value`

**[E-VAR]**
```
(Γ, x ↦ v) ⊢ x ⇓ v
```

**[E-APP]**
```
Γ ⊢ e₁ ⇓ λx.e    Γ ⊢ e₂ ⇓ v₂    Γ[x ↦ v₂] ⊢ e ⇓ v
─────────────────────────────────────────────────────
Γ ⊢ e₁ e₂ ⇓ v
```

**[E-IF-TRUE]**
```
Γ ⊢ e₁ ⇓ true    Γ ⊢ e₂ ⇓ v
──────────────────────────────
Γ ⊢ if e₁ e₂ e₃ ⇓ v
```

**[E-IF-FALSE]**
```
Γ ⊢ e₁ ⇓ false    Γ ⊢ e₃ ⇓ v
───────────────────────────────
Γ ⊢ if e₁ e₂ e₃ ⇓ v
```

**[E-WHILE-FALSE]**
```
Γ ⊢ e₁ ⇓ false
─────────────────────
Γ ⊢ while e₁ e₂ ⇓ ()
```

**[E-WHILE-TRUE]**
```
Γ ⊢ e₁ ⇓ true    Γ ⊢ e₂ ⇓ ()    Γ ⊢ while e₁ e₂ ⇓ ()
──────────────────────────────────────────────────────
Γ ⊢ while e₁ e₂ ⇓ ()
```

### 3.5 Compilation Rules

**Statement Compilation:**

```python
def compile_stmt(s):
    match s:
        case VarDecl(x, τ, e):
            return compile_expr(e) + [STORE(x)]
        
        case Assignment(x, e):
            return compile_expr(e) + [STORE(x)]
        
        case IfStmt(cond, then, else_):
            L1, L2 = fresh_label(), fresh_label()
            return (
                compile_expr(cond) +
                [JMPF(L1)] +
                compile_stmt(then) +
                [JMP(L2), LABEL(L1)] +
                compile_stmt(else_) +
                [LABEL(L2)]
            )
        
        case WhileStmt(cond, body):
            L_start, L_end = fresh_label(), fresh_label()
            return (
                [LABEL(L_start)] +
                compile_expr(cond) +
                [JMPF(L_end)] +
                compile_stmt(body) +
                [JMP(L_start), LABEL(L_end)]
            )
```

**Expression Compilation:**

```python
def compile_expr(e):
    match e:
        case Literal(n):
            return [PUSH(n)]
        
        case Var(x):
            return [LOAD(x)]
        
        case BinOp(e1, op, e2):
            return (
                compile_expr(e1) +
                compile_expr(e2) +
                [BINOP(op)]
            )
        
        case Call(f, args):
            code = []
            for arg in args:
                code += compile_expr(arg)
            return code + [CALL(f, len(args))]
```

### 3.6 Instruction Set (Internal IR)

```
LOAD var           # Push variable onto stack
STORE var          # Pop stack into variable
PUSH const         # Push constant
POP                # Discard top of stack
CALL func arity    # Call function with arity args
RET                # Return from function
JMP label          # Unconditional jump
JMPF label         # Jump if false (pop stack)
BINOP op           # Binary operation
SPAWN              # Create entity (Ndando primitive)
REPAIR             # Attempt repair (Ndando primitive)
CANONIZE           # Mark canonical (Ndando primitive)
```

### 3.7 Type Safety Guarantees

**Progress Theorem:**
```
If Γ ⊢ e : τ and e is not a value,
then there exists e' such that e → e'
```

**Preservation Theorem:**
```
If Γ ⊢ e : τ and e → e',
then Γ ⊢ e' : τ
```

**Type Safety (Combined):**
```
If ∅ ⊢ e : τ, then either:
  - e ⇓ v where ∅ ⊢ v : τ, or
  - e ⇓ Failure, or
  - e diverges
```

---

## 4. NDANDO-P: INTERPRETED LANGUAGE EXECUTION MODEL

### 4.1 Abstract Machine Definition

**Ndando-P Abstract Machine (NPAM)**

```
NPAM = (Frames, Heap, Globals, PC, CallStack)

Where:
  Frames = Stack of execution frames
  Heap = Garbage-collected object heap
  Globals = Global namespace dictionary
  PC = Program counter (bytecode index)
  CallStack = Function call stack
```

**Frame Structure:**
```python
Frame = {
    'code': Bytecode,
    'pc': int,
    'locals': dict[str, Value],
    'stack': list[Value],
    'prev_frame': Optional[Frame]
}
```

### 4.2 Execution Cycle

```python
def execute_frame(frame):
    while frame.pc < len(frame.code):
        instr = frame.code[frame.pc]
        frame.pc += 1
        
        try:
            execute_instruction(instr, frame)
        except Exception as e:
            handle_exception(e, frame)
        
        if return_called(frame):
            return pop_frame(frame)
```

### 4.3 Interpretation Pipeline

```
Ndando-P Source
    ↓
[Lexical Analysis + Indentation Processing]
    ↓
Token Stream (with INDENT/DEDENT)
    ↓
[Parsing]
    ↓
Abstract Syntax Tree
    ↓
[Desugaring to Ndando-C]
    ↓
Ndando-C AST
    ↓
[Type Inference (optional)]
    ↓
[Compilation to Ndando-A]
    ↓
Ndando-A Instructions
    ↓
[Execution on NAAM]
```

### 4.4 Desugaring Rules

**Function Definition:**
```
def f(x):
    body

⟶

function f(x: infer(x)) {
    body
}
```

**While Loop:**
```
while condition:
    body

⟶

loop {
    if not condition break
    body
}
```

**For Loop:**
```
for x in iterable:
    body

⟶

tmp_iter = iterable.iterator()
while tmp_iter.has_next():
    x = tmp_iter.next()
    body
```

**Context Manager:**
```
with resource as r:
    body

⟶

tmp = resource
tmp.acquire()
r = tmp
try:
    body
finally:
    tmp.release()
```

**Try-Except:**
```
try:
    body
except E as e:
    handler
finally:
    cleanup

⟶

try_block(body)
catch(E, handler)
finally_block(cleanup)
```

### 4.5 Dynamic Type Inference

**Runtime Type Tracking:**

```python
def infer_type(expr, env):
    match expr:
        case NumberLiteral(n):
            return Int if isinstance(n, int) else Float
        
        case StringLiteral(s):
            return String
        
        case BoolLiteral(b):
            return Bool
        
        case Identifier(x):
            return lookup_type(env, x)
        
        case BinOp(e1, op, e2):
            t1 = infer_type(e1, env)
            t2 = infer_type(e2, env)
            return infer_binop_type(op, t1, t2)
        
        case Call('spawn', [arg]):
            return Seed
        
        case Call('repair', [arg]):
            arg_type = infer_type(arg, env)
            return Union(arg_type, None)
```

### 4.6 Operational Semantics (Big-Step)

**Environment:** `ρ : Var → Value`

**[E-NUM]**
```
⟨n, ρ⟩ ⇓ n
```

**[E-VAR]**
```
ρ(x) = v
─────────
⟨x, ρ⟩ ⇓ v
```

**[E-BINOP]**
```
⟨e₁, ρ⟩ ⇓ v₁    ⟨e₂, ρ⟩ ⇓ v₂    v = eval_op(op, v₁, v₂)
────────────────────────────────────────────────────────
⟨e₁ op e₂, ρ⟩ ⇓ v
```

**[E-IF-TRUE]**
```
⟨e₁, ρ⟩ ⇓ true    ⟨e₂, ρ⟩ ⇓ v
──────────────────────────────
⟨if e₁: e₂ else e₃, ρ⟩ ⇓ v
```

**[E-WHILE]**
```
⟨e₁, ρ⟩ ⇓ false
─────────────────────
⟨while e₁: e₂, ρ⟩ ⇓ None

⟨e₁, ρ⟩ ⇓ true    ⟨e₂, ρ⟩ ⇓ ρ'    ⟨while e₁: e₂, ρ'⟩ ⇓ v
──────────────────────────────────────────────────────────
⟨while e₁: e₂, ρ⟩ ⇓ v
```

**[E-SPAWN]**
```
⟨e, ρ⟩ ⇓ v    create_seed(v) = s
──────────────────────────────────
⟨spawn(e), ρ⟩ ⇓ s
```

**[E-REPAIR]**
```
⟨e, ρ⟩ ⇓ failure    attempt_repair(failure) = Some(v)
───────────────────────────────────────────────────────
⟨repair(e), ρ⟩ ⇓ v

⟨e, ρ⟩ ⇓ failure    attempt_repair(failure) = None
──────────────────────────────────────────────────
⟨repair(e), ρ⟩ ⇓ None
```

### 4.7 Memory Management

**Garbage Collection:**
- Mark-and-sweep collector for heap objects
- Reference counting for cycles detection
- Generational collection for performance

**Memory Model:**
```
Heap Objects:
  - All Ndando types (Seed, Tree, Forest, etc.)
  - User-defined structures
  - Function closures

Stack:
  - Local variables (frame-scoped)
  - Temporary values
  - Call frames

Globals:
  - Module-level bindings
  - Imported symbols
```

---

## 5. CROSS-LAYER EXECUTION SEMANTICS

### 5.1 Type Preservation Across Layers

**Theorem (Type Preservation):**
```
If Γ ⊢ e : τ in Ndando-P
and desugar(e) = e' in Ndando-C
and compile(e') = e'' in Ndando-A
then execute(e'') produces value v : τ
```

**Proof Sketch:**
- Base cases preserve types trivially
- Inductive cases preserve types by desugaring/compilation rules
- NAAM type system ensures runtime preservation

### 5.2 Semantic Equivalence

**Behavioral Equivalence:**
```
e₁ ≈ e₂ iff ∀ρ. ⟨e₁, ρ⟩ ⇓ v₁ ∧ ⟨e₂, ρ⟩ ⇓ v₂ → v₁ = v₂
```

**Compilation Correctness:**
```
For any well-typed Ndando-P program p:
  ⟦p⟧_P ≈ ⟦desugar(p)⟧_C ≈ ⟦compile(desugar(p))⟧_A
```

### 5.3 Execution Flow Diagram

```
┌─────────────────────────────────────────┐
│         Ndando-P Source Code            │
│  (def, while, for, with, try/except)    │
└──────────────┬──────────────────────────┘
               │
               ▼
┌─────────────────────────────────────────┐
│    Lexer (indentation-aware)            │
│  Tokens: INDENT, DEDENT, NEWLINE        │
└──────────────┬──────────────────────────┘
               │
               ▼
┌─────────────────────────────────────────┐
│    Parser (builds AST)                  │
│  Tree structure with position info      │
└──────────────┬──────────────────────────┘
               │
               ▼
┌─────────────────────────────────────────┐
│    Desugarer (P → C transformation)     │
│  - Flatten control structures           │
│  - Explicit resource management         │
└──────────────┬──────────────────────────┘
               │
               ▼
┌─────────────────────────────────────────┐
│    Type Checker (Hindley-Milner)        │
│  - Infer types                          │
│  - Unify constraints                    │
│  - Check interfaces                     │
└──────────────┬──────────────────────────┘
               │
               ▼
┌─────────────────────────────────────────┐
│    Optimizer (optional)                 │
│  - Constant folding                     │
│  - Dead code elimination                │
│  - Inline expansion                     │
└──────────────┬──────────────────────────┘
               │
               ▼
┌─────────────────────────────────────────┐
│    Code Generator (C → A)               │
│  - Flatten to instructions              │
│  - Allocate registers/stack             │
│  - Generate canonical form              │
└──────────────┬──────────────────────────┘
               │
               ▼
┌─────────────────────────────────────────┐
│    NAAM (Ndando-A Abstract Machine)     │
│  Components:                            │
│  - Instruction Pointer                  │
│  - Operand Stack                        │
│  - Ledger (SEL logging)                 │
│  - Canon Store                          │
│  - Memory Map                           │
└──────────────┬──────────────────────────┘
               │
               ▼
┌─────────────────────────────────────────┐
│         CivOS Kernel Runtime            │
│  - Execute primitives (spawn, repair)   │
│  - Manage lifecycle                     │
│  - Enforce OCEAN-1 constraints          │
│  - Log to Jiwe (canonical memory)       │
└─────────────────────────────────────────┘
```

---

## 6. IMPLEMENTATION GUIDELINES

### 6.1 Reference Implementation Architecture

**Recommended Stack:**

```
┌─────────────────────────────────────┐
│   Ndando-P Parser (Python/Rust)     │
│   - Lexer with indentation          │
│   - Recursive descent parser        │
│   - AST builder                     │
└─────────────────────────────────────┘
            ↓
┌─────────────────────────────────────┐
│   Ndando-C Type Checker             │
│   - Hindley-Milner inference        │
│   - Constraint solver               │
│   - Error reporting                 │
└─────────────────────────────────────┘
            ↓
┌─────────────────────────────────────┐
│   Ndando-A Code Generator           │
│   - Instruction emission            │
│   - Label resolution                │
│   - Optimization passes             │
└─────────────────────────────────────┘
            ↓
┌─────────────────────────────────────┐
│   NAAM Virtual Machine              │
│   - Stack-based execution           │
│   - Garbage collection              │
│   - SEL integration                 │
│   - Safety checks                   │
└─────────────────────────────────────┘
```

### 6.2 Performance Considerations

**Time Complexity:**
- Parsing: O(n) where n = source length
- Type inference: O(n log n) with efficient unification
- Compilation: O(n) linear passes
- Execution: O(m) where m = instruction count

**Space Complexity:**
- Parser: O(depth) for AST
- Type checker: O(variables) for environment
- Compiler: O(instructions)
- Runtime: O(live_objects + stack_depth)

### 6.3 Safety Mechanisms

**Required Safety Checks:**

1. **Type Safety:**
   - Static type checking in Ndando-C
   - Runtime type validation in Ndando-P
   - Type preservation across compilation

2. **Memory Safety:**
   - Bounds checking on arrays/stacks
   - No use-after-free (GC or ownership)
   - Canon immutability enforcement

3. **Execution Safety:**
   - Stack overflow detection
   - Infinite loop detection (optional)
   - Resource quota enforcement

4. **Ledger Integrity:**
   - Append-only SEL
   - Cryptographic signatures (optional)
   - Tamper detection

### 6.4 Testing Strategy

**Unit Tests:**
- Individual operator semantics
- Type inference edge cases
- Compilation correctness
- Runtime primitives

**Integration Tests:**
- Full pipeline (P → C → A → execution)
- Type preservation across layers
- Semantic equivalence verification
- Error propagation

**Property-Based Tests:**
- Type safety (Progress + Preservation)
- Semantic equivalence
- Determinism
- Termination (where applicable)

### 6.5 Debugging Support

**Debug Information:**
```python
class DebugInfo:
    source_file: str
    line_number: int
    column_number: int
    function_name: str
    local_vars: dict[str, Value]
    stack_trace: list[Frame]
```

**Tracing Modes:**
- Instruction-level trace (NAAM)
- Statement-level trace (Ndando-C)
- Expression-level trace (Ndando-P)
- SEL audit trail (all layers)

### 6.6 Error Handling

**Error Categories:**

```
E001 - Syntax error
E002 - Undefined identifier
E003 - Type mismatch
E004 - Arity mismatch
E005 - Invalid operator for type
E010 - Memory access violation
E011 - Clause 11 violation (missing meta-annotation)
E012 - Canon write violation
E013 - Ledger corruption
E020 - Interface mismatch
E021 - Module not found
E030 - Package signature invalid
E031 - Version conflict
E040 - Repair failed
E041 - MLE forecast failure (high-risk)
E042 - Adaptation impossible
E050 - Resource exhaustion
E051 - Stack overflow
E052 - Heap exhaustion
E060 - Governance violation
E061 - Unauthorized operation
E070 - Runtime panic
```

---

## 7. FORMAL VERIFICATION

### 7.1 Type Safety Proofs

**Progress Theorem (Ndando-C):**

```
∀e, τ. (∅ ⊢ e : τ ∧ e ∉ Values) ⟹ ∃e'. e → e'

Proof by induction on typing derivation:
- Base cases: literals and variables are values
- Inductive cases: application, if, while all make progress
```

**Preservation Theorem (Ndando-C):**

```
∀e, e', τ. (∅ ⊢ e : τ ∧ e → e') ⟹ ∅ ⊢ e' : τ

Proof by induction on reduction relation:
- Each reduction step preserves types
- Substitution lemma ensures type preservation
```

### 7.2 Semantic Preservation

**Theorem (Compilation Correctness):**

```
∀p ∈ Ndando-P. 
  well_typed(p) ⟹
    ⟦p⟧_P = ⟦desugar(p)⟧_C = ⟦compile(desugar(p))⟧_A

Proof sketch:
- Desugaring is semantics-preserving transformation
- Compilation generates equivalent instruction sequences
- NAAM execution follows small-step semantics
```

### 7.3 Termination Analysis

**Termination for Ndando-A:**

```
Programs may not terminate due to:
1. Explicit recursion (forest >> kernel)
2. While loops without guaranteed exit
3. Repair/adapt cycles

Decidability: Termination is undecidable in general
```

**Termination Checking:**
- Structural recursion checker
- Loop variant analysis
- Repair depth limits

---

## 8. OPTIMIZATION TECHNIQUES

### 8.1 Compile-Time Optimizations

**Constant Folding:**
```python
# Before
x = 2 + 3
y = x * 4

# After (compile-time)
x = 5
y = 20
```

**Dead Code Elimination:**
```python
# Before
if False:
    expensive_operation()

# After
# (removed entirely)
```

**Inline Expansion:**
```python
# Before
def add(a, b):
    return a + b
x = add(1, 2)

# After
x = 1 + 2
```

### 8.2 Runtime Optimizations

**JIT Compilation:**
- Hot path detection
- Dynamic compilation to native code
- Profile-guided optimization

**Memory Optimization:**
- Object pooling for common types
- String interning
- Lazy evaluation where safe

---

## 9. STANDARD LIBRARY INTEGRATION

### 9.1 Core Primitives

All standard library functions compile to Ndando-A primitives:

```
spawn(Type) → >> operator
repair(Object) → ~> operator
adapt(Object) → ~~> operator
grow(Seed) → ^ operator
mycorrhizate(T1, T2) → <> operator
canonize(Object) → ## operator
```

### 9.2 Library Implementation Pattern

```python
# Ndando-P library function
def stabilize(system):
    """Stabilize a system through repair cycles."""
    max_attempts = 5
    for attempt in range(max_attempts):
        if detect_drift(system):
            system = repair(system)
        else:
            return system
    
    # If repair fails, adapt
    return adapt(system)

# Compiles to Ndando-A sequence:
# :set max_attempts 5
# :loop
#   :detect_drift system
#   :jumpf stable
#   ~> system
#   :dec max_attempts
#   :jumpnz loop
# :stable
#   ~~> system
```

---

## 10. CONCLUSION

This specification defines the complete execution and computational models for the Ndando language family. Key properties:

- **Deterministic execution** at all layers
- **Type safety** through static checking (Ndando-C) and dynamic validation (Ndando-P)
- **Semantic preservation** across compilation pipeline
- **Auditability** through comprehensive SEL logging
- **Safety** through explicit effects and memory management

Implementation conformance requires adherence to:
1. Operational semantics as specified
2. Type system rules
3. Memory safety guarantees
4. Ledger logging requirements
5. OCEAN-1 constitutional constraints

---

## APPENDIX A: QUICK REFERENCE

### Operator Summary

| Operator | Arity | Type Signature | Semantics |
|----------|-------|----------------|-----------|
| `^` | 2 | `T₁ → T₂ → T₂` | Grow/elevate |
| `>>` | 2 | `T → Seed → Seed` | Spawn entity |
| `!` | 1 | `Project → Program` | Boot program |
| `~` | 1 | `Program → Cycle` | Run program |
| `@` | 1 | `Cycle → Process` | Execute cycle |
| `#` | 1 | `Process → Process` | Process step |
| `->` | 2 | `T₁ → T₂` | Map/transform |
| `<>` | 2 | `Forest → Forest → Coupling` | Mycorrhizate |
| `\|\|` | 1+ | `T → [T]` | Fork/cleave |
| `X` | 1 | `T → Failure` | Collapse |
| `~>` | 1 | `Failure → T` | Repair |
| `~~>` | 1 | `Failure → T` | Adapt |
| `?` | 1 | `T → Decision` | Decide |
| `##` | 1 | `T → Canon<T>` | Canonize |
| `==` | 2 | `T → T → Bool` | Equality |
| `!=` | 2 | `T → T → Bool` | Inequality |

### Execution Cycle Summary

| Layer | Cycle | Complexity |
|-------|-------|------------|
| Ndando-A | Fetch→Decode→Validate→Execute→Log→Update→Check | O(1) per instruction |
| Ndando-C | Parse→TypeCheck→Optimize→CodeGen→Execute | O(n log n) compilation |
| Ndando-P | Lex→Parse→Desugar→Infer→Lower→Execute | O(n log n) interpretation |

---

**END OF SPECIFICATION**
