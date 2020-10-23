# The Record About Indirect Call Analysis
Record all question while analyzing indirect call.

# libwx_gtk2u_core
## ICall in Loop
**0x2bc270**: 
~~~Assembly
call [rax+8]
~~~

## ICall for Switch
**0x2fc4dc**: <BV64 0x48a3fc + t14>
~~~Assembly
lea rdx, off_48a3fc
movsxd rax, [rdx+rax*4]
add rdx, rax
jmp rdx
~~~

## ICall has Complex Expression
**0x33ef0b**: <BV64 Load((0xffffffffffffffff + (t4 + t9)))>
~~~Assembly
mov rcx, [rax+rcx-1]
jmp rcx
~~~

**0x33e81e**: (*TODO*)
var: <BV64 Load((0x58 + Load((if xxx then (0x398 + r40) else (0x378 + r40)))))>
~~~Assembly
lea rbp, [rbx+398h]
lea rdx, [rbx+378h]
test al, 10h
cmovz rbp, rdx

mov rax, [rbp+0]
call [rax+60h]
~~~


## ICall Example
**3502d1**:
~~~Assembly
mov rcx, [rax+rcx-1]
jmp rcx
~~~

## How to Get the SP Variable
**example**:
~~~Assembly
sub rsp, 1F8h
mov [rsp], rsi
~~~


## Arguments Recognition
### The Register Arguments
**x64**: (rdi, rsi, rdx, rcx, r8, r9)

### The Stack Arguments
**TODO**

## Callee Define Arguments
### Argument is Stack Variable
**0x3e074c**: (*TODO*)
~~~Assembly
lea rax [rsp+28h+var_20]
mov [rsp+28h+var_20], 0
call Quantize

mov rdi, [rsp+28h_var_20]
mov rax, [rdi]
call [rax+10]
~~~
The argument is stack variable, and the callee define this variable which always initial defined with 0.

## Functoin Return Value Recognition

## Fast Generate CFG
Fast generate control flow graph by record IDA function graph.

### Class: CFGBlock
Each cfg block contains the block's irsb, start and end addr.
* vptrs_xref: a list for saving vtable pointer
* icalls: a list for saving indirect call
### Class: IDABlock
Each ida block contains one or more cfg block.

## How to solve the return value of new/malloc etc.
*TODO*

## Solve the Kill Definition
Example 1:
~~~Assembly
Load(esp + 0x108) = rdi

rax = Load(esp + 0x108)
Load(rax + rdx) = 0x745df8; vptr

Put(rax) = 0xab
Load(rdi + 24) = rdx
~~~

Example 2:
If the pointer store is kill defined, the definition is alive before redefined.
Think about the callee function that use the definition.
~~~Assembly
Load(rdi + 0x80) = vptr
call func
...
Load(rdi + 0x80) = 0xcd; kill definition
~~~

Example 3:
~~~Assembly
@@@--> Analyze <Block 0x278e00, (0x278e00)>
@@@-->DEBUG: ptrs [<Expr <BV64 t20>: <BV64 0x76c0a0>>]
@@@-> DEBUG: new expr: <Expr <BV64 t9>: <BV64 0x76c0b0>>
@@@-> DEBUG: new expr: <Expr <BV64 r152>: <BV64 0x76c0a0>>
@@@-> DEBUG: new expr: <Expr <BV64 r16>: <BV64 0x76c0b0>>
@@@-> DEBUG: new expr: <Expr <BV64 Load(t19)>: <BV64 0x76c0b0>>
~~~

## The variable's alive period
After the variable is redefined, the life cycle of the previous variable is closed.

~~~
PUT(rcx) = 0x8
t11 = GET(rdi)
...
t5 = GET(rbx)
t2 = LDle(t5)
PUT(rax) = t2; expr = load(load(t2 + 0x20) + rcx) trace_vars = ['t2', 'rcx']
    expr_old = load(load(rax + 0x20) + rcx) trace_vars=['rcx'], killed_vars=['rax']
...
t9 = Add(t11, 0x104)
STle(t9) = t2

alive_expr = load(load(rax + 0x20) + rcx);  trace_vars = ['rax', 'rcx']
~~~

## Alias Name
~~~Assembly
mov rbx, rdi
mov rax, cs:dword_7dbb10
mov [rdi], rax

alias variable: rax, load(rdi), load(rbx)

t19 = GET:I64(rdi)
PUT(rbx) = t19
t20 = LDle:I64(0x00000000007dbb10)
t9 = Add64(t20,0x0000000000000010)
PUT(rax) = t9
STle(t19) = t9
~~~

* save vtable ptr to stack
~~~Assembly
mov rax, vtable_ptr
mov [rsp+0x108], rax

trace_expr = load(rsp+0x108)
should use forward to find alias, not backward.
~~~

* save constant global ptr
~~~Assembly
expr = load(0x743de4)

mov rax, 0x743de4
mov [rdi+0x8], rax
~~~
should replace 0x743de4 with load(rdi+0x8)

## Forward and Back Trace
To find the alias name of a variable, for example (rax=func_ptr, rax=new/malloc, etc.)
**t20 = ptr**: for the tmp variable 't20', only need to find alias name by forwarding; 
**rax = ptr**: for the register 'rax', only need to find alias name by forwarding;
**deref(t5+0x24) = ptr**: for tmp variable 't5', could find alias name by forwarding and backing;
**deref(rdi+0x24) = ptr**: for register variable 'rdi', could find alias name by forwarding and backing;

## Get the Successor Block Forward Expr
~~~
<Expr <BV64 t20>: <BV64 0x76c0a0> (F)>
<Expr <BV64 t9>: <BV64 0x76c0b0> (F)>
<Expr <BV64 r152>: <BV64 0x76c0a0> (F)>
<Expr <BV64 r16>: <BV64 0x76c0b0> (F)>
<Expr <BV64 Load(t19)>: <BV64 0x76c0b0> (F)>
<Expr <BV64 Load(r40)>: <BV64 0x76c0b0> (F)>
<Expr <BV64 Load(r72)>: <BV64 0x76c0b0> (F)>
~~~

# IRSB Example
~~~
   00 | ------ IMark(0x3e05f0, 4, 0) ------
   01 | t0 = GET:I64(rsp)
   02 | t5 = LDle:I64(t0)
   03 | PUT(rax) = t5
   04 | ------ IMark(0x3e05f4, 3, 0) ------
   05 | t3 = GET:I64(r13)
   06 | PUT(cc_op) = 0x0000000000000014
   07 | PUT(cc_dep1) = t3
   08 | PUT(cc_dep2) = 0x0000000000000000
   09 | PUT(pc) = 0x00000000003e05f7
   10 | ------ IMark(0x3e05f7, 3, 0) ------
   11 | t6 = GET:I64(rbx)
   12 | STle(t5) = t6
   13 | PUT(pc) = 0x00000000003e05fa
   14 | ------ IMark(0x3e05fa, 2, 0) ------
   15 | t15 = CmpEQ64(t3,0x0000000000000000)
   16 | t14 = 1Uto64(t15)
   17 | t12 = t14
   18 | t16 = 64to1(t12)
   19 | t7 = t16
   20 | if (t7) { PUT(pc) = 0x3e0604; Ijk_Boring }
   NEXT: PUT(rip) = 0x00000000003e05fc; Ijk_Boring
~~~

# Read Vtable Ptr Problem
~~~Assembly
0x280003
lea rax, off_76C6F0
...
mov [rbx], rax
~~~

~~~Assembly
0x29400a
lea rax, 0ff_76f7d0
mov [rsp+88h+var_88], rax
call wxRegion::~wxRegion()
~~~

# Call Graph has Loop Problem
## 0x2d7cf0
The icall and vtable ptr info.
~~~
DEBUG: block <Block 0x2d80e0, (0x2d7cf0)> has vtalbe ptr
@@@--> vtable: <Expr <BV64 t11>: <BV64 0x77d3c0> (F)>
DEBUG: block <Block 0x2d8e84, (0x2d7cf0)> has vtalbe ptr
@@@--> vtable: <Expr <BV64 t17>: <BV64 0x77be60> (F)>
DEBUG: block <Block 0x2d7dda, (0x2d7cf0)> has vtalbe ptr
@@@--> vtable: <Expr <BV64 t9>: <BV64 0x77a800> (F)>
DEBUG: block <Block 0x2d811c, (0x2d7cf0)> has vtalbe ptr
@@@--> vtable: <Expr <BV64 t14>: <BV64 0x77f740> (F)>
DEBUG: block <Block 0x2d8e3f, (0x2d7cf0)> has vtalbe ptr
@@@--> vtable: <Expr <BV64 t12>: <BV64 0x77b720> (F)>
@@@--> vtable: <Expr <BV64 t13>: <BV64 0x76c580> (F)>
DEBUG: block <Block 0x2d8f39, (0x2d7cf0)> has icall ptr
@@@--> icall: <Expr <BV64 t8> (B)>
DEBUG: block <Block 0x2d8cca, (0x2d7cf0)> has icall ptr
@@@--> icall: <Expr <BV64 t3> (B)>
DEBUG: block <Block 0x2d83f4, (0x2d7cf0)> has icall ptr
@@@--> icall: <Expr <BV64 t7> (B)>
DEBUG: block <Block 0x2d8d32, (0x2d7cf0)> has icall ptr
@@@--> icall: <Expr <BV64 t3> (B)>
~~~

# The Class FindLoop
FindLoop used to find all loops in a function.
**be careful**: the node in Loop's body_nodes is a copy of function graph. So we should analyze the function graph's node, not the node in Loop.

## Class FindLoop Warning
('Bad loop: more than one entry point (%s, %s)', <Block 0x473b88, (0x473ab0)>, <Block 0x473b9f, (0x473ab0)>)
('Bad loop: more than one entry point (%s, %s)', <Block 0x2f28c0, (0x2f2810)>, <Block 0x2f2899, (0x2f2810)>)
('Bad loop: more than one entry point (%s, %s)', <Block 0x3a4dc5, (0x3a4b90)>, <Block 0x3a4e91, (0x3a4b90)>)
('Bad loop: more than one entry point (%s, %s)', <Block 0x3a4d03, (0x3a4b90)>, <Block 0x3a4c46, (0x3a4b90)>)
('Bad loop: more than one entry point (%s, %s)', <Block 0x3a2dc0, (0x3a2cf0)>, <Block 0x3a2dfa, (0x3a2cf0)>)

# Ignore some special registers.
In x64, following registers could be ignored.
~~~
 144: 'cc_op',
 152: 'cc_dep1',
 160: 'cc_dep2',
 168: 'cc_ndep',
~~~
We add 'used_max_offseti = 136' in arch_amd64.py, if the register's offset over 136, we ignore them.

# How to solve the redefined
We use the post-dominator to solve the variable redefined problem.

# How to solve stack varialbe
## Example one
~~~Assembly
   00 | ------ IMark(0x2f2ae0, 5, 0) ------
   01 | t9 = GET:I64(rsp)
   02 | t8 = Add64(t9,0x0000000000000020)
   03 | PUT(rbx) = t8
~~~

## Example two
For the stack store, should only trace by forward.
~~~
t8 = Get(rsp)
t19 = Add(t8, 0x40)
STle(t19) = t20
~~~

# Summary definition in loop
## Example one (0x2f2810)
~~~
<Expr <BV64 Load((0x1d8 + Load(Load((0x30 + (r48 + (0x8 + r40)))))))> (B)>
<Expr <BV64 Load((0x1d8 + Load(Load((0x30 + (r48 + (0x8 + (0x8 + r40))))))))> (B)>
~~~
**TODO**

## Example tow (0x3d3220)

# Make Copy whlle Tracing
Each expr has a different index in each block.

# The Object is Delete
~~~
.text:00000000002BC4E9 mov     rdi, r12        ; void *
.text:00000000002BC4EC call    __ZdlPv         ; operator delete(void *)
~~~

# Ignore some operators in Claripy
we igonre some special ops in Claripy, and replace them with symbol 'u'
self.ignore_ops = ['Extract', 'Concat', 'ZeroExt', 'SignExt']
~~~
   00 | ------ IMark(0x384767, 2, 0) ------
   01 | PUT(pc) = 0x0000000000384769
   02 | ------ IMark(0x384769, 4, 0) ------
   03 | t22 = GET:I64(rbp)
   04 | t21 = Add64(t22,0x0000000000000008)
   05 | t5 = LDle:I64(t21)
   06 | t24 = GET:I64(rax)
   07 | t23 = 64HLto128(0x0000000000000000,t24)
   08 | t7 = DivModU128to64(t23,t5)
   09 | t46 = 128HIto64(t7)

   <BV64 t7[127:64]>, op: Extract
   replaced with <BV64 u>
~~~

# Claripy Simplify
The simplify will change the var's __hash__(), and create a new var
~~~
<BV64 Load(__add__(0x20, (t15 + ((t10 + (t10 * 0x8)) * 0x8)), (0x48 * Load((0x20 + r48))), (0xffffffffffffffb8 * i)))>
~~~

## claripy concrete
~~~
claripy.operations.leaf_operations_concrete
{'BVV', 'BoolV', 'FPV'}
~~~

# Do it Future!
## How to find the stack def

## Each variable has a special alive

