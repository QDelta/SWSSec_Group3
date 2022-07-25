### Abstract

Buffer overflows are a weakness commonly found in some languages such as C and Java. Any code without a strict boundary limitation can have potential overflow risk and it's easy to be unaware of them. We demonstrate an approach to verification of C-like programs using analysis of the source code of programs. The approach uses a formal definition of the syntax and semantics of the subset of C and makes use of symbolic execution. Our approach is shown to capture all overflows of the source code written in our object language.

#### Keyword

buffer overflow, vulnerability in programs, static analysis, symbolic execution



### 1. Introduction

Buffer overflow is a common vulnerability in programs.  Many attacks on Microsoft systems are based on various buffer overflow problems. However, in some commonly used languages like C or Java, these problems won't be pointed out by the compiler. 

In this paper, we will use symbol execution to discover buffer overflow problems in small programs which are written in the subset of C and develop an analyzing application with a GUI.



### 2. Background

#### 2.1 A glance at Buffer overflow attack

Buffer overflow, as its name suggest, occurs when a program attempts to write more data to a fixed-length block of memory, or buffer, than the buffer is allocated to hold. Once an overflow occurs, the extra data will overwrite data value in adjacent memory addresses of destination buffer. This consequence can be used to crash a process or modify its internal variables. The attack which is based on this consequence is called buffer overflow attack.

This kind of attack can be fatal because the original data in the buffer includes the exploited function's return pointer. The attacker can use the extra data to modify these pointers and modify the address to which the process should go next according to their own wishes. For example, they can make it point to a dangerous attacking program and finish their attack easily.

Besides, buffer overflow attack ranks high in Common Weakness Enumeration (CWE). This kind of vulnerability can occur easily in programs without sufficient bounds checking. The preventing work can be sophisticated especially when the occurrence of this kind of vulnerable problems won't always be warned by the compiler. As a result, an assistant tool with a function of checking potential overflow risk can be meaningful.

#### 2.2 Symbol execution overview

Symbolic execution is a way of executing a program abstractly. This kind of execution treats the inputs of the program symbolically and focuses on execution paths through the code. To be more specific, the result of a symbolic execution should be expressed in terms of symbolic constants that represent the input values. 

By doing one abstract execution, multiple possible inputs of the program that share a particular path can be covered. Besides, symbol execution also has another strength, that is it can avoid giving false warnings because each of all these errors represents a particular path through the program. This provides us an idea of checking potential buffer-overflow. For any program statement which has the possibility of occurring buffer-overflow problem, we can check the value range of those involved variables to verify whether they satisfied the boundary constrains. If any of these variables fail to meet the condition, we can say that a buffer-overflow problem occurs.



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

The general process of the analysis includes several parts. 

The first part includes two preparation work. One is to check whether the source code can be compiled successfully. Another is to do an initial analyzation with a parser and gain abstract syntax tree of the code. The purpose of this step is to transform the code into an abstract form for the following analyzation.

In the second part, we will use symbolic execution to extract useful information from the result of the first step, and generate counter-examples of the variables involved in statements which have the risk of occurring buffer-overflow. 【已修改】

Next, a SMT-solver will be used to check whether any of these counter-examples can be satisfied. We will have a deeper discussion on how this solver can be used in part 4.3. With the feedback from the solver, we can locate the potential buffer-overflows in the source code. 【已修改】

The last part of our analysis is to print the errors discovered to a GUI.

The whole process can also be illustrated by the diagram below.

*（I plan to add a diagram here to  demonstrate the whole process, I'll add the image here later）

Now, we will explain each part respectively.

#### 4.1 Preparation

The first part of the preparation is to get the source code the user input and compile it. Our goal is to discover those potential risks which cannot be warned by the compiler and our target source code should be those which can compile. If an error occurs, we will print the error information to the output box and halt the whole process.

Only if a source code can compile, will it be given to a parser to generate a abstract syntax tree. We use pycparser here, which is a parser of C and written in Python. It can be replace by any parser of C. The output will then be the input of the next part. 【加了一点点东西。。想了一下这块再写的话内容确实太多了】

#### 4.2 From program to counter-examples

The goal of this part is to generate counter-examples. In this part, we will use symbolic execution. 【已修改】

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
Now we can introduce our idea of generating counter-examples with symbolic execution. We can treat the boundary conditions as assumptions for particular statement and use path condition $P$ to describe them. For each statement, $E$ and $P$ should be satisfied at the same time, that is, $E \wedge P$ should always be true. In this case,  $\overline{E\wedge P}$ will be the counter-examples. However, it's unnecessary to check all of the statements. Only for those statements who have a risk of occurring buffer-overflow, do we need to do generate counter-examples. To do this, we can write rules for evaluating programs symbolically. Here we listed several different forms of the rules. 【已修改】

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

To get an intuition for what we can get from the process, we can take the code above (function $foo()$ with assumption) as an example.

After execution, the generated counter-examples will be【已修改】

```
n'>0 and h'>=n'*4 and head'!=0 and (0>0*4 or 0*4>=h),
n'>0 and h'>=n'*4 and head'==0 and (0>n'*4 or n'*4>=h)
```

With the rules, we can write a program to realize this function. 【已修改】

#### 4.3 Counter-example analysis

【整块已修改】

The goal for this step is to check whether any of the counter-examples we get from 4.2 can be satisfied.

Suppose that we now get a set of counter-examples $C_i$, $i=1...n$. We should check each of them. If a particular counter-example can be satisfied, the line where we generate it could have overflow risk. Now the question has transformed to whether there exists a mapping from symbolic constants to input values, that $C_i=true$. 

So far, we've transformed our original problem into a satisfiability problem. We can use SMT-solver z3 to solve it and find out the counter-examples which maybe unsatisfied. The statement where we generate them are the errors we found.



### 5. GUI and running results

After previous work, we have located the errors. The last stage of the analysis is to print these errors. In this part, we will provide some example codes and their running results.

*(I plan to add some examples and the pictures of the running results as well as our GUI. Besides, I also plan to add some brief explanations on the result we get, such as why is a particular line highlighted and in what  situation could buffer-overflow occur for a particular statement.）



### 6. Related works and comparison

【已完善】

In the method we mentioned above, we're actually doing static analysis. There's also another way to test vulnerability of programs, which is called dynamic analysis. Unlike static analysis, dynamic analysis evaluates the program by executing data in real-time. The input cases can be generated by a program using random algorithm, or be typed in by the tester.

What these two kind of methods have in common is that they're both trying to find counter-examples. Though dynamic analysis can prove a program has overflows, it can be overwhelmed when faced with a correct program. The method we mentioned, on the other hand, uses static analysis and attempt to find counter-examples in a more theoretical way, which allows it to prove the non-existence of counter-examples.

Besides, our method has another advantage over dynamic analysis in efficiency. While a particular input case can only find out some of the buffer-overflows, symbolic execution can check every possible path in the program. This allows us to find all the errors with only one execution instead of testing endlessly.

### 7. Conclusion

【已修改】

From the represented results we can see that our method owns advantages of precision, efficiency and automation. However, there are also some shortages. First is that the solver we use in counter-examples analysis (4.3) is unstable.  The reason is that the satisfiability problem we are trying to solve is a NP problem. The second shortage is that since the process gives another program as the input of our program, it can't handle any program according to the halting problem.

However, most of the cases, our method can perform well and give a correct result quickly. So we can still say that the advantages overweigh the disadvantages and this method can be of help in testing programs for vulnerabilities.



### 8. References

[1] Aldrich, J. Symbolic Execution (Program Analysis lecture notes - Spring 2019). Retrieved from https://www.cs.cmu.edu/~aldrich/courses/17-355-19sp/notes/notes14-symbolic-execution.pdf#:~:text=Symbolic%20execution%20is%20a%20way%20of%20executing%20a,of%20symbolic%20constants%20that%20represent%20those%20input%20values

[2] Hugh Anderson. Topic9-MachineArchitectureBW.pdf



### Appendix

（排版的时候看看怎么把上面的公式搬下来）

