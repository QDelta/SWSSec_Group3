### Abstract



#### Keyword



### 1. Introduction

Buffer overflow is a common vulnerability in programs.  Many attacks on Microsoft systems are based on various buffer overflow problems. However, in some commonly used languages like C or Java, these problems won't be pointed out by the compiler. 

In this paper, we will use symbol execution to discover buffer overflow problems in small programs which are written in the subset of C and develop an analyzing application with a GUI.

（大致思路：简述buffer overflow问题，然后简单写一下我们干的事）



### 2. Background

#### 2.1 A glance at Buffer overflow attack

Buffer overflow, as its name suggest, occurs when a program attempts to write more data to a fixed-length block of memory, or buffer, than the buffer is allocated to hold. Once an overflow occurs, the extra data will overwrite data value in adjacent memory addresses of destination buffer. This consequence can be used to crash a process or modify its internal variables. The attack which is based on this consequence is called buffer overflow attack.

This kind of attack can be fatal because the original data in the buffer includes the exploited function's return pointer. The attacker can use the extra data to modify these pointers and modify the address to which the process should go next according to their own wishes. For example, they can make it point to a dangerous attacking program and finish their attack easily.

Besides, buffer overflow attack ranks high in Common Weakness Enumeration (CWE). This kind of vulnerability can occur easily in programs without sufficient bounds checking. The preventing work can be sophisticated especially when the occurrence of this kind of vulnerable problems won't always be warned by the compiler. As a result, an assistant tool with a function of checking potential overflow risk can be meaningful.

（大致的想法：定义说一下，然后这玩意危害性大，但是容易出现，所以一个checker是很有帮助的）

#### 2.2 Symbol execution overview

Symbolic execution is a way of executing a program abstractly. This kind of execution treats the inputs of the program symbolically and focuses on execution paths through the code. To be more specific, the result of a symbolic execution should be expressed in terms of symbolic constants that represent the input values. 

By doing one abstract execution, multiple possible inputs of the program that share a particular path can be covered. Besides, symbol execution also has another strength, that is it can avoid giving false warnings because each of all these errors represents a particular path through the program. This provides us an idea to check potential buffer-overflow. For any program statement which has the possibility of occurring buffer-overflow problem, we can check the value range of those involved variables to verify whether they satisfied the boundary constrains. If any of these variables fail to meet the condition, we can say that a buffer-overflow problem occurs.

### 3. Definition of language

To simplify the process, we set the language of the source code to a subset of C. For the convenience of illustrating our ideas, we will use a less complicated language (we may call the language SymC--), which is semantically a subset of C, to descript our object language. Here are the detailed definitions.

Expression:
$$
\begin{align*}
e ::=\ \ &n &\mathrm{integer\ literal}\\
  |\ \ &x &\mathrm{name}\\
  |\ \ &e\ bop\ e &\mathrm{binary\ operation}\\
  |\ \ &uop\ e &\mathrm{unary\ operation}\\
  |\ \ &\texttt{alloc}(e) &\mathrm{memory\ allocation}
\end{align*}
$$

Statement:
$$
\begin{align*}
s ::=\ \ &\texttt{skip} &\mathrm{empty\ statement}\\
  |\ \ &\texttt{declint}\ x &\mathrm{integer\ declaration}\\
  |\ \ &\texttt{declptr}\ x &\mathrm{pointer\ declaration}\\
  |\ \ &x\leftarrow e &\mathrm{assignment}\\
  |\ \ &\texttt{touch}\ e[e] &\mathrm{memory\ access}\\
  |\ \ &s;s &\mathrm{sequence}\\
  |\ \ &\texttt{if}\ e\ \texttt{then}\ s\ \texttt{else}\ s &\mathrm{conditional}
\end{align*}
$$

Values:
$$
\begin{align*}
v ::=\ \ &\texttt{int}\ v_i &\mathrm{integer}\\
  |\ \ &\texttt{ptr}\ v_i\ v_i &\mathrm{pointer\ with\ bounds}\\
v_i ::=\ \ &n &\mathrm{concrete\ integer}\\
  |\ \ &x &\mathrm{symbolic\ integer}\\
  |\ \ &uop\ v_i &\mathrm{unary\ operation}\\
  |\ \ &v_i\ bop\ v_i &\mathrm{binary\ operation}\\
  |\ \ &\texttt{ite}\ a\ v_i\ v_i &\mathrm{conditional}
\end{align*}
$$

Assertions:
$$
\begin{align*}
a ::=\ \ &v_i\ relop\ v_i &\mathrm{integer\ relation}\\
  |\ \ &\lnot a &\mathrm{negation}\\
  |\ \ &a\land a &\mathrm{conjunction}\\
  |\ \ &a\lor a &\mathrm{disjunction}
\end{align*}
$$

It's also necessary to emphasize that this demo language sharing the same semantics with our source code language won't be involved in our code implementation. The purpose of introducing such language is just for the convenience of illustration.

### 4. Process of analysis

（这个地方先简单说一下整个流程，然后后面开始分点细讲）

The general process of the analysis includes several parts. 

The first part includes two preparation work. One is to check whether the source code can be compiled successfully. Another is to do an initial analyzation with a parser and gain abstract syntax tree of the code. The purpose of this step is to transform the code into an abstract form for the following analyzation.

In the second part, we will use symbolic execution to extract useful information from the result of the first step, and generate constrains of the variables involved in statements which have the risk of occurring buffer-overflow.

Next, a SMT-solver will be used to check whether any of these constrains are not satisfied. We will have a deeper discussion on how this solver can be used to check those conditions in part 4.3. With the result of the solver, we can locate the potential buffer-overflows in the source code.

The last part of our analysis is to print the errors discovered to a GUI.

The whole progress can also be illustrated by the diagram below.

（画一个流程图表示一下整个过程）

Now, we will explain each part respectively.

#### 4.1 Preparation

（首先是通过compiler排除编译错误的信息，然后简单写一下overview中第一部分，既程序->抽象语法树的部分）

The first part of the preparation is to get the source code the user input and compile it. Our goal is to discover those potential risks which cannot be warned by the compiler and our target source code should be those which can compile. If an error occurs, we will print the error information to the output box and halt the whole process.

Only if a source code can compile, will it be given to a parser to generate a abstract syntax tree. We use pycparser here. The output will then be the input of the next part.

#### 4.2 From program to constrains

（写代码的核心部分，defs.md中的第二段各种表达式用在这里）

The goal of this part is to extract constrains. In this part, we will use symbolic execution. 

First, we will give a more specific illustration of this method.

When we do symbolic execution, we are actually executing a path through the source code. During this process, we will track values of variables and the conditions needed to be satisfied for particular path. It's necessary to mention that the values that we will keep track of are all expressed in terms of symbolic constants. For example, if $a=1$ and $b=a+1$, then the values we track should be
$$
\begin{align*}
\alpha&=1,\beta=1\\
a&=\alpha,b=a+\beta=\alpha+\beta\\
\end{align*}
$$
In this example, $\alpha$ and $\beta$ are the symbolic constants, and $a=\alpha,b=\alpha+\beta$ is what we will keep track of. We can use symbolic environment $E$ as a collective name for the mapping from name to value that we keep track of.

To have a clearer picture of the process, we can take the code below as an example.

```c
void foo(int *arr, int n, int head) {
    if (head) {
        print(arr[0]);
    } else {
        print(arr[n]);
    }
}
```

In this function, we will track the value of $arr$, $n$, and $head$. Their symbolic constants are $ptr\ h', n'$ and $head'$. The symbolic environment $E$ looks like this.
$$
\begin{align*}
E=\{arr=ptr\ h',\ n=n',\ head=head'\}
\end{align*}
$$
When we meet conditional statement, we will track the condition for each branch. When we come to the first branch, the path condition $P$ we will be tracking is $head'>0$. For the second branch, the path condition $P$ is $head'\leq 0$. The symbolic environment $E$ is not updated in this function.

If there are any assumption in the source code, it should be described by symbolic environment $E$ and path condition $P$.

```c
void foo(int *arr, int n, int head) {
    ASSUME(n > 0, capacity(arr) >= n * sizeof(int));
    if (head) {
        print(arr[0]);
    } else {
        print(arr[n]);
    }
}
```

For example, if we add an assumption at the beginning of the function, $E$ and $P$ should be look like this when after executing the assumption statement.
$$
\begin{align*}
E&=\{arr=ptr\ h',\ n=n',\ head=head'\}\\
P&=\{n'>0,\ h'\leq n'*4\}
\end{align*}
$$
Now we can introduce our idea of generating constrains with symbolic execution. We can treat the boundary conditions as assumptions for particular statement and use path condition $P$ to describe them. For each statement, $E$ and $P$ should be satisfied at the same time, that is, $E \wedge P$ should always be true. However, it's unnecessary to check all of the statements. Only for those statements who have a risk of occurring buffer-overflow, do we need to generate a constraint. To do this, we can write rules for evaluating programs symbolically. Here we listed several different forms of the rules.

Evaluation rules in the form of $E;e\Downarrow v$. It means expression $e$ is evaluated to value $v$ in environment $E$.
$$
\frac{}{E;n\Downarrow \texttt{int}\ n}
\quad
\frac{}{E;x\Downarrow E(x)}
$$

$$
\frac{E;e\Downarrow \texttt{int}\ v}{E;uop\ e\Downarrow \texttt{int}\ (uop\ v)}
\quad
\frac{E;e_1\Downarrow \texttt{int}\ v_1\quad E;e_2\Downarrow \texttt{int}\ v_2}
{E;e_1\ bop\ e_2\Downarrow \texttt{int}\ (v_1\ bop\ v_2)}
$$

$$
\frac{E;e_1\Downarrow \texttt{ptr}\ l\ h\quad E;e_2\Downarrow \texttt{int}\ v}
{E;e_1+e_2\Downarrow \texttt{ptr}\ (l-v)\ (h-v)}
\quad
\frac{E;e_1\Downarrow \texttt{int}\ v\quad E;e_2\Downarrow \texttt{ptr}\ l\ h}
{E;e_1+e_2\Downarrow \texttt{ptr}\ (l-v)\ (h-v)}
$$

$$
\frac{E;e_1\Downarrow \texttt{ptr}\ l\ h\quad E;e_2\Downarrow \texttt{int}\ v}
{E;e_1-e_2\Downarrow \texttt{ptr}\ (l+v)\ (h+v)}
$$

$$
\frac{E;e\Downarrow\texttt{int}\ v}
{E;\texttt{alloc}(e)\Downarrow\texttt{ptr}\ 0\ v}
$$

Execution rules in the form of $E,P;s\Downarrow E';C$. It means given environment $E$ and path condition $P$, after executing the statement $s$ the environment will be updated to $E'$ and counter examples $C$ will be generated.

Path condition $P$ is an assertion. $C$ is the set of generated assertions that should not be satisfied.

$$
\frac{}{E,P;\texttt{skip}\Downarrow E;\{\}}
$$

$$
\frac{}{E,P;\texttt{declint}\ x\Downarrow E \cup\{x\mapsto \texttt{int}\ x'\};\{\}}
$$

$$
\frac{}{E,P;\texttt{declptr}\ x\Downarrow E \cup\{x\mapsto \texttt{ptr}\ 0\ 0\};\{\}}
$$

$$
\frac{E;e\Downarrow v}{E,P;x\leftarrow e\Downarrow E[x\mapsto v];\{\}}
$$

$$
\frac{E,e_1\Downarrow \texttt{ptr}\ l\ h\quad E,e_2\Downarrow\texttt{int}\ v}
{E,P;\texttt{touch}\ e_1[e_2]\Downarrow E;\{P\land (l>v\lor v\ge h)\}}
$$

$$
\frac{E,P;s_1\Downarrow E';C_1\quad E',P;s_2\Downarrow E'';C_2}
{E,P;s_1;s_2\Downarrow E'';C_1\cup C_2}
$$

$$
\frac{E;e\Downarrow \texttt{int}\ v\quad E,P\land v\ne 0;s_1\Downarrow E_1;C_1\quad E,P\land v=0;s_2\Downarrow E_2;C_2}
{E,P;\texttt{if}\ e\ \texttt{then}\ s_1\ \texttt{else}\ s_2\Downarrow \mathrm{merge}(v,E_1,E_2);C_1\cup C_2}
$$

$\mathrm{merge}(v,E_1,E_2)=E$ means $\forall x\in E_1,E_2$:

$$
E_1(x)=\texttt{int}\ v_1,E_2(x)=\texttt{int}\ v_2 \\
\rightarrow E(x)=\texttt{int}\ (\texttt{ite}\ (v=0)\ v_2\ v_1)
$$

$$
E_1(x)=\texttt{ptr}\ l_1\ h_1,E_2(x)=\texttt{ptr}\ l_2\ h_2 \\
\rightarrow E(x)=\texttt{ptr}\ (\texttt{ite}\ (v=0)\ l_2\ l_1)\ (\texttt{ite}\ (v=0)\ h_2\ h_1)
$$

else error.

To get an intuition for what we can get from the process, we can take the code (function $foo()$ with assumption) above as an example.

After execution, the generated counter examples will be

```
n'>0 and h'>=n'*4 and head'!=0 and (0>0*4 or 0*4>=h),
n'>0 and h'>=n'*4 and head'==0 and (0>n'*4 or n'*4>=h)
```

With the rules, we can write a program to generate the constraints.

#### 4.3 Constraint analysis

The goal for this step is to check whether any of the constraints we get from 4.2 is not satisfied.

For a set of conditions $C_i$, $i=1...n$, if any of them is not satisfied, $\bigcap C_i=false$. According to De Morgan's laws, we have$\overline{\bigcap C_i}=\bigcup \overline{C_i}$ . Now the question has transformed to whether there exists a mapping from symbolic constants to input values, that $\bigcup \overline{C_i}=true$. 

So far, we've transformed our original problem into a satisfiability problem. We can use SMT-solver z3 to solve it and find out the conditions which maybe unsatisfied. The statement where we generate those false conditions are the errors we found.

### 5. GUI and running results

（GUI界面设计，运行结果展示）

After previous work, we have located the errors. The last stage of the analysis is to print these errors. In this part, we will provide some example codes and their running results.

（一些example和GUI的图片，然后对运行结果做一个简单的解释比如报错的某个地方可能出现怎样的buffer-overflow）

### 6. Conclusion

Buffer-overflow is a commonly seen vulnerability of program and can be fatal. Although we can't gain warnings from the compiler, static analysis can also be available. By using symbolic execution, we can locate the vulnerable statements precisely. This can be of help in testing programs for vulnerabilities.

### 7. References

symbolic execution 那篇文章应该怎么写引用？

Topic9-MachineArchitectureBW.pdf（这个好像也不太知道怎么写引用。。）









