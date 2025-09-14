# Assertion-based-verification

# SystemVerilog Assertions (SVA)

## `Overview`:
``SystemVerilog Assertions (SVA)`` are powerful constructs used primarily to validate the behavior of RTL designs. They provide a compact, efficient way to verify design properties compared to traditional Verilog checkers, making it easier to catch bugs early in the design process. Assertions significantly increase observability and controllability during verification.

## `Advantages Over Traditional Verilog Checkers`:
1. `Compact Code`: SVA provides concise syntax for complex checks
2. `Enhanced Debugging`: Easier to identify and locate design bugs
3. `Improved Verification`: Increases observability (monitoring internal states) and controllability (triggering specific scenarios)
5. `Temporal Capabilities`: Support for complex sequence and property checking across multiple clock cycles.

## `Assertion Types`:
### 1. `Immediate Assertions`:

`Evaluation Time:` Current simulation time (like procedural code)

`Characteristics:`
1. Evaluated immediately when encountered in procedural code
2. Multiple assertions can lead to glitches if not properly handled
3. Can be declared inside classes, modules, and interfaces

`Syntax`:
```
assertion_label: assert (expression) 
    [pass_statement;] 
    [else fail_statement;]

```
`Example`:
```
always @(posedge clk) begin
    check_valid: assert (valid) else $error("Valid signal not asserted");
end
```

`NOTE`: 
#### Deferred Immediate Assertions:
To avoid glitches from multiple assertions, use #0 or final keywords:
```
// Using #0 deferral
assert #0 (a && b) else $error("Check failed");

// Using final (executes at end of time slot)
assert final (enable && ready) else $warning("Enable without ready");

```


## 2. `Concurrent Assertions`:
`Evaluation Time`: Sampled in pre-poned region, evaluated in observed region

`Characteristics`:
1. Use the property keyword to define complex temporal behavior
2. Clock-based evaluation across multiple cycles
3. Can only be declared in modules, interfaces, and programs (not in classes)
4. More efficient for checking design properties over time

`Syntax`:
```
property property_name;
    [clocking_event] expression_or_sequence;
endproperty

assertion_label: assert property (property_name) 
    [pass_statement;] 
    [else fail_statement;]
Property Definition:

```
`Example`:
```
property req_ack_prop;
    @(posedge clk) req |-> ##[1:3] ack;
endproperty

assert property (req_ack_prop) else $error("Ack not received within 3 cycles");
```
```
// Direct inline assertion
assert property (@(posedge clk) enable |-> ##1 ready) 
    else $error("Ready not asserted after enable");

```
## 📋 Comparison Table: `Immediate vs Concurrent Assertions`
```
 _________________________________________________________________________________________________________________________
| Aspect                  | Immediate Assertions                         | Concurrent Assertions                          |
|_________________________|______________________________________________|________________________________________________|
| Evaluation Time         | Current simulation time                      | Sampled in pre-poned, evaluated in observed    |
| Declaration Scope       | Classes, modules, interfaces                 | Modules, interfaces, programs (not classes)    |
| Clock Dependency        | No explicit clock                            | Requires explicit clocking event               |
| Temporal Capabilities   | Limited to current time                      | Extensive (sequences, repetition across cycles)|
| Glitch Sensitivity      | High (multiple assertions cause glitches)    | Low (uses sampled values)                      |
| Deferral Mechanism      |  #0 or final keywords                        | Built-in sampling mechanism                    |
| Syntax Structure        | assert (expression)                          | assert property (property_name)                |
| Property Keyword        | Not used                                     | Requires property definition                   |
| Sequence Support        | No                                           | Yes (sequence keyword supported)               |
| Simulation Overhead     | Lower (immediate evaluation)                 | Higher (temporal evaluation)                   |
| Typical Use Cases       | Procedural checks, class validation          | Design property verification, protocol checking|
|_________________________|______________________________________________|________________________________________________|

```

## Operator Comparison: `Immediate vs Concurrent`

```
 _________________________________________________________________________________________
| Operator           | Immediate Assertions        | Concurrent Assertions                |
|____________________|_____________________________|______________________________________|
| Logical AND        |        &&                   |        &&                            |
| Logical OR         |        ||                   |        ||                            |
| Implication        | Not available               |      ->  or  =>                      |
| Sequence Delay     | Not available               | ##n                                  |
| Temporal Range     | Not available               | ##[min:max]                          |
| Sampled Value      | Current value               | $sampled(expression)                 |
| Clock Event        | Not used                    | @(posedge clk)                       |
| Reset Condition    | Manual handling             | disable iff (condition)              |
|____________________|_____________________________|______________________________________|

```


## SystemVerilog Temporal Operators — Assertions

This document explains the main temporal operators in SystemVerilog Assertions (SVA):  
1. `within`
2. `until`
3. `until_with`
4. `throughout`
5. `or`
6. `and`
7. `not`
8. `intersect`

Each section has a short theory and waveform diagrams for **PASS** and **FAIL** cases.

---

## ⏳ 1. `within`:

**Theory:**  
`A within B` means that the sequence `A` must **start and end completely during** the time `B` is true.  
If `A` goes beyond `B`'s active duration, the assertion fails.

### ✅ PASS
```
Time →   0   1   2   3   4   5   6
         |   |   |   |   |   |   |
A:       ____|‾‾‾|___

B:   ____|‾‾‾‾‾‾‾‾‾‾‾‾|___
```

### ❌ FAIL
```
Time →   0   1   2   3   4   5   6
         |   |   |   |   |   |   |
A:       ___|‾‾‾‾‾‾‾‾‾|___

B:   ___|‾‾‾‾‾|___
```

---

## ⏳ 2. `until`:

**Theory:**  
`A until B` means `A` must stay **continuously true until** `B` becomes true.  
Once `B` is true, the checking of `A` stops (A can be 0 afterwards).

### ✅ PASS
```
Time →   0   1   2   3   4   5
         |   |   |   |   |   |
A:      _|‾‾‾‾‾‾‾|___________

B:                ___|‾‾|___
```

### ❌ FAIL
```
Time →   0   1   2   3   4   5
         |   |   |   |   |   |
A:      _|‾‾‾|___|‾‾‾|______

B:                   ____|‾‾|___
```


## ⏳ 3. `until_with`:

**Theory:**  
`A until_with B` means `A` must stay **true until and also on the same cycle** when `B` becomes true.  
If `A` is low on the cycle `B` becomes high, it fails.

### ✅ PASS
```
Time →   0   1   2   3   4   5
         |   |   |   |   |   |
A:       |‾‾‾‾‾‾‾‾‾‾‾|____

B:                  _|‾‾‾|___
```

### ❌ FAIL
```
Time →   0   1   2   3   4   5
         |   |   |   |   |   |
A:       |‾‾‾|‾‾‾|___|___
B:                   ___|‾‾|___
```

---

## ⏳ 4. `throughout`:

**Theory:**  
`A throughout B` means whenever `B` is active, `A` must be **true on every cycle**.  
If `A` goes low during `B`, the assertion fails.

### ✅ PASS
```
Time →   0   1   2   3   4   5
         |   |   |   |   |   |
A:       |‾‾‾‾‾‾‾‾‾‾‾‾‾|__

B:           ___|‾‾‾‾‾‾|___
```

### ❌ FAIL
```
Time →   0   1   2   3   4   5
         |   |   |   |   |   |
A:       |‾‾‾|___|‾‾‾|_____

B:           ____|‾‾‾‾‾‾|___
```

---

---

## 5. `or (Sequence OR)`

**Theory:**  
`A or B` means **either sequence `A` or sequence `B` must occur to satisfy the property.**

### ✅ PASS
```
clk   :  _|‾‾‾|___|‾‾‾|___|‾‾‾|___|‾‾‾|_
seq A :  _|‾‾‾|__
seq B :          _|‾‾‾|__
         <either A or B occurs>
```

### ❌ FAIL
```
clk   :  _|‾‾‾|___|‾‾‾|___|‾‾‾|___|‾‾‾|_
seq A :  _________
seq B :  _________
       <neither A nor B occurs>
```

---
---
## 6. `and (Sequence AND)`:

**Theory:**  
`A and B` means **both sequences `A` and `B` must occur and end at the same time.**

### ✅ PASS
```
clk   :  _|‾‾‾|___|‾‾‾|___|‾‾‾|___|‾‾‾|_
seq A :          _|‾‾‾|__
seq B :          _|‾‾‾|__
            <both occur in parallel>
```

### ❌ FAIL
```
clk   :  _|‾‾‾|___|‾‾‾|___|‾‾‾|___|‾‾‾|_
seq A :  _|‾‾‾|__
seq B :          _|‾‾‾|__
            <not aligned => FAIL>
```
---

---

## 7. `not (Sequence Negation)`:

**Theory:**  
`not A` means the **sequence `A` must never occur** during evaluation. If it occurs even once, it fails.

### ✅ PASS
```
clk :  _|‾‾|__|‾‾|__|‾‾|__|‾‾|__

A   :  ___________________________
      <never occurs => PASS>
```

### ❌ FAIL
```
clk :  _|‾‾|__|‾‾|__|‾‾|__|‾‾|__

A   :        _|‾‾|__
          <A occurs => FAIL>
```

---
---
## 8. `intersect (Parallel Intersection)`:

**Theory:**  
`A intersect B` means **both sequences `A` and `B` must occur completely and must overlap exactly** in time.

### ✅ PASS
```
clk   :  __|‾‾‾|___|‾‾‾|___|‾‾‾|_

seq A :           _|‾‾‾|__
seq B :           _|‾‾‾|__

      <overlap exactly => PASS>
```

### ❌ FAIL
```
clk   :  __|‾‾‾|___|‾‾‾|___|‾‾‾|_

seq A :   _|‾‾‾|__
seq B :           _|‾‾‾|__
      <misaligned => FAIL>
```
---

##  `Summary Table`:
```
 ___________________________________________________________________________________________
| Operator        |              Meaning                                                    |
|_________________|_________________________________________________________________________|
| `within`        | A starts and ends completely within B’s active time.                    |
| `until`         | A stays true until B becomes true (before one edge).                    |
| `until_with`    | A stays true until and also on the same cycle B becomes true.           |
| `throughout`    | A must be true on every cycle while B is active.                        |
| `or`            | Either sequence A or sequence B must occur to satisfy the property.     |
| `and`           | Both sequences A and B must occur and end at the same time.             |
| `not`           | The sequence A must never occur during evaluation.                      |
| `intersect`     | Both sequences A and B must occur completely and overlap exactly in time|
|_________________|_________________________________________________________________________|


```



