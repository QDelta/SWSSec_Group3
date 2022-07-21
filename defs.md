We may call the language SymC--, which is semantically a subset of C. We use this language to illustrate our ideas.

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

Environment $E$ is a mapping from name to value

Evaluation rules in the form of $E;e\Downarrow v$. It means expression $e$ is evaluated to value $v$ in environment $E$:
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

Path condition $P$ is an assertion

$C$ is the set of generated assertions that should not be satisfied

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

C example
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
translate to our demo language
```
if head then
  touch arr[0]
else
  touch arr[n]
```

translate parameters and assumption to initial environment and path condition
```
E = {arr: ptr 0 h', n: int n', head: int head'}
P = n'>0 and h'>=n'*4
```

after execution, the generated counter examples will be
```
n'>0 and h'>=n'*4 and head'!=0 and (0>0*4 or 0*4>=h),
n'>0 and h'>=n'*4 and head'==0 and (0>n'*4 or n'*4>=h)
```

the first is not satisfiable, report a pass

the second is satisfiable, report an error