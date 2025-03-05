# Example: checking mergeability through overflows

Suppose that $v_1$ is a view with shape
$(10, 3, 3)$ and strides $(\sigma_1, \sigma_2, \sigma_3)$
and we want to merge it with a view $v_2$ with shape $(s)$ and stride $(4)$;
this is a simple case, because $v_2$ is only one dimensional.

In this example, we are going to see that $v_1$ and $v_2$ are mergeable if $s \leq 4$
and $\sigma_1 = 2 \sigma_2 + 3 \sigma_3$ hold.
However, if $s > 4$, then for $v_1$ and $v_2$ to be mergeable,
we additionally require that $\sigma_1 = 3 \sigma_2$ holds.
The example will hopefully convince you that the only way to find out which equations need to hold,
is to check which "overflows" occur, for which you need to iterate over all indices $i = 0, \ldots, s - 1$.

To do this, we're going to check the main criterion in this repo: informally,
it says that for every increase in the
index $i$ of view $v_2$, we need to jump exactly by some constant $\sigma$,
which is going to be the stride of the merged tensor view.

Let's first recall the definition:
$v_1$ and $v_2$ can be merged if the function
`v1.index_fn ∘ unravel v1.shape ∘ v2.index_fn` can be expressed as `v.index_fn`,
where `v` is a view with shape $(s)$ (the same shape as $v_2$) and some stride $(\sigma)$.
The index function is the function that maps an index in the tensor to its position in memory
(this is the inner product with the stride),
and the unraveled index function is that same function, but precomposed with the unravel function
`Nat -> IndexSet v1.shape`. See the main [README](../README.md) for a more elaborate explanation.

Let's now do the calculations for our example.
This means that for every $0 \leq i < s$,
we are first going to calculate `(unravel v1.shape ∘ v2.index_fn) i`,
i.e., which index $(i_1, i_2, i_3)$ in the tensor `v1` corresponds to index `i` in `v2`.
Then we are going to calculate `v1.index_fn` of that tensor,
which gives us the position in memory.

Suppose first that the shape of $v_2$ is 4, so that we have the indices $i = 0, 1,2,3$.
For example, if $i = 1$, then the index function of $v_2$ gives 4 (because the stride is 4),
and unravelling that to the shape $(10, 3, 3)$ gives us the index
$(i_1, i_2, i_3) = (0, 1, 1)$.
The table below shows this for all indices,
and on the right in the row corresponding to the index $i$,
it shows the equation that the criterion gives us when you go from index $i - 1$ to index $i$.
So for example, for $i = 1$, 
the the index function of $v_1$ sends $(0,0,0)$ to 0,
and it sends $(0, 1, 1)$ to $\sigma_1 \cdot 0 + \sigma_2 \cdot 1 + \sigma_3 \cdot 1 = \sigma_2 + \sigma_3$.
This needs to be an increase by exactly $\sigma$, so in other words,
we need to have $\sigma = \sigma_2 + \sigma_3$.
We can do this calculation for every increase in $i$, giving us the following table:


| $i$ | $i_1$ | $i_2$ | $i_3$  | eqn |
| --- | --- | --- | ---  | --- |
|  0  |  0  | 0 | 0      |     |
|  1  |  0  | 1 | 1      |  $\sigma = \sigma_2 + \sigma_3$   |
|  2  |  0  | 2 | 2      |  $\sigma = \sigma_2 + \sigma_3$   |
|  3  |  1  | 1 | 0      |  $\sigma_1 + \sigma_2 = 2 \sigma_2 + 2 \sigma_3 + \sigma$   |

We see that in the step from $i = 2$ to $i = 3$, we have 2 overflows occurring at the same time:
the third index flows over to the second, and the second flows over to the first.
This calculation is very similar to the arithmetic you learnt in elementary school,
where you also had to deal with overflow, but in a [mixed radix](https://en.wikipedia.org/wiki/Mixed_radix) numeral system:
instead of a decimal numeral system (every position has 10 possible values)
or a hexadecimal numeral system (every position has 16 possible values),
each position can have a different number of possible values,
and the number of values is given by the shape!

We can solve all these linear equations: it gives us $\sigma_1 = 2 \sigma_2 + 3 \sigma_3$ and $\sigma = \sigma_2 + \sigma_3$; i.e., we can choose $\sigma_2, \sigma_3$ however we want, and then
$\sigma_1$ and $\sigma$ are determined by the equations.
In conclusion, we found that we can merge the view $v_1$ and the view $v_2$ as long as
the linear equation $\sigma_1 = 2 \sigma_2 + 3 \sigma_3$ holds.
(This is what I sometimes referred to as an "accidental mergeability", because
it is based on a double overflow, where you get a different kind of equation
that you don't ordinarily encounter.)

Now suppose, however, that the shape of $v_2$ wasn't $(4)$, but $(6)$. Then we'd get the following
table with the following equations:


| $i$ | $i_1$ | $i_2$ | $i_3$  | eqn |
| --- | --- | --- | ---  | --- |
|  0  |  0  | 0 | 0      |     |
|  1  |  0  | 1 | 1      |  $\sigma = \sigma_2 + \sigma_3$   |
|  2  |  0  | 2 | 2      |  $\sigma = \sigma_2 + \sigma_3$   |
|  3  |  1  | 1 | 0      |  $\sigma_1 + \sigma_2 = 2 \sigma_2 + 2 \sigma_3 + \sigma$   |
|  4  |  1  | 2 | 1      |  $\sigma = \sigma_2 + \sigma_3$    |
|  5  |  2  | 0 | 2      |  $2 \sigma_1 + 2 \sigma_3 = \sigma_1 + 2 \sigma_2 + \sigma_3 + \sigma$    |

Note that we now had 2 different overflows:

- when going from $i = 2$ to $i = 3$, index $i_2$ overflowed to $i_1$ and index $i_3$ overflowed to index $i_2$ simultaneously
- when going from $i = 4$ to $i = 5$, we only have a single overflow from $i_2$ to $i_1$.


Because these overflows are different, we get different equations.
The linear equations coming from $i = 0$ up to $i = 3$ gave us the equations
$\sigma = \sigma_2 + \sigma3$ and $\sigma_1 = 2 \sigma_2 + 3 \sigma_3$.
Now we have the additional equation
$2 \sigma_1 + 2 \sigma_3 = \sigma_1 + 2 \sigma_2 + \sigma_3 + \sigma$;
plugging in the previous equations, this can be rewritten as $\sigma_1 = 3 \sigma_2$.
This means we get an additional equation, so it is possible
that $v_1$ and $v_2$ are mergeable when $s$ is at most 4,
while they are not mergeable anymore when $s > 4$!
The only way we could have found the exact set of equations that need to hold,
is by iterating through the indices, and checking which kinds of overflows you get.
(Unless there is some very smart way of finding overflows? If you know how to do that,
please send me a message!)


## Observations


- the generic case is only a single overflow, and the double overflow is more "accidental"
- if all the single overflows are valid, then more complex overflows are automatically valid too
- we saw a double overflow, but you can have an arbitrary set of indices overflowing at the same time
- you can easily and completely generally write down the equations that come from overflows; e.g. for a single overflow from $i_j$ to $i_{j-1}$, the equation is always $\sigma_{j-1} = s_j \sigma_j$ (which non-coincidentally is also the equation you get for the canoncical strides in a new tensor)
