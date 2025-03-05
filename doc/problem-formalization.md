# Problem formalization


### Views

**Definition** A *view* is a tuple $(s, \sigma)$ of a shape $s = (s_1, \ldots, s_k)$, $s_i \in \mathbb N$, and a set of strides $\sigma = (\sigma_1, \ldots, \sigma_k)$, $\sigma_i \in \mathbb N$.

The interpretation of this is as follows: with respect to some given contiguous and linear array of data $d$, a view $v = (s, \sigma)$ represents a tensor of shape $s$, with the coordinate $[i_1, \ldots, i_k]$ corresponding to the data point $d[ \sum_j i_j \sigma_j]$.

This interpretation of a view $v$ is with respect to a linear array of data $d$, but you can also have a view $v$ into a tensor rather than into a linear array.
I explain how to do this in [the section "Formalization of a view into a tensor"](#formalization-of-a-view-into-a-tensor-rather-than-into-an-array);
(you need to "unravel").

### Merging views

Now we can clarify the concept of *merging* two views. I'll give the intuitive idea in this section, and then the formalization in a section below ("Formalization of merging two views").

Suppose we have a pair of views $(v, v')$. (Note: the order of the pair matters.) We can consider the composition of these two views: given some underlying linear array, we can view it as a tensor through $v$, and then we can view into that tensor through $v'$. This resulting tensor is the composition.

We say that $(v, v')$ can be *merged* into a view $v'' = (s'', \sigma'')$ if the view $v''$ represents the same tensor as the composition of $(v, v')$. Not every composition can be represented by a single view!

### Problem statement

For performance reasons, we would like to merge views into a single view without changing the memory layout.

**Goal**: the goal of this repo is to formally prove in Lean a simple criterion for whether two views can or can not be merged.

This is analogous to e.g. checking the determinant of a matrix: a matrix is invertible if and only if the determinant is 0. Before you try to invert the matrix, you can easily check if the determinant is 0, and possibly save yourself some time. Here we'd like to have something similar: before you try to merge two views, it would be nice if a simple criterion could tell us whether or not the views are mergeable.

With a successful completion of the problem statement, we will get two performance boosts:

1. We can check that we always merge views if possible
2. We do not need to try to merge if merging is impossible

## Formalization of a view into a tensor (rather than into an array)

This section formalizes the concept of composing and merging two views.

Suppose we have a shape $s = (s_1, \ldots, s_k)$. The standard contiguous view for such a shape is the row-major view made precise below.

**Definition** Let $s = (s_1, \ldots, s_k)$ be a shape. Define *the contiguous view for $s$* as the view $v^s = (s, \sigma^s = (\sigma^s_1, \ldots, \sigma^s_k))$ , where

$$\sigma_j^s = \prod_{\ell=j+1}^k s_\ell$$

We have defined views as a tuple $v = (s, \sigma)$, but we can also consider them as functions in the following way. Let $I_s$ denote the set of valid indices for the shape $s$, i.e.,

$$I_s = \{(i_1, \ldots, i_k) \in \mathbb N : \forall 1 \leq \ell \leq k, 0 \leq i_\ell < s_\ell \}.$$

Then $v$ represents the function

$$v \colon I_s \to \mathbb N, \quad (i_1, \ldots, i_k) \mapsto \sum_\ell i_\ell \sigma_\ell$$

The notion of having a view $v$ into a tensor of shape $s'$ can now be formalized as the following function:

$$ (v^{s'})^{-1} \circ v \colon I_s \to I_{s'}$$

This corresponds precisely to the intuition laid out before: $(v^{s'})^{-1}$ does the reverse of laying out the tensor into a linear piece of data in row-major form.

Note: $(v^{s'})^{-1}$ is known as un1d in the tinygrad code.

## Formalization of merging two views

**Definition** The composition of two views $v = (s, \sigma), v' = (s', \sigma')$ represents the map into linear data space defined by

$$ v \circ (v^s)^{-1} \circ v'$$

In words, this can be interpreted as follows: given indices for the shape $s'$, you first map them into linear data through $v'$; then you consider these indices as coming from a tensor of shape $s$ (this is what is done by $(v^s)^{-1}$); and finally, you consider this tensor that you've mapped it into as a view through $v$.


**Definition** Two views $(v, v')$ can be merged into a view $v''$ if the function represented by their composition (i.e., $v \circ (v^s)^{-1} \circ v'$) is equal to the function represented $v''$.



## Misc

I posted an earlier draft of this document as [an issue in the tinygrad repo](https://github.com/tinygrad/tinygrad/issues/8194).
Other people continued the discussion [on this issue](https://github.com/tinygrad/tinygrad/issues/8511).