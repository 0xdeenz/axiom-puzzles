# Tuple Filtering

The goal of this puzzle is to write a Circom circuit constraining filtering from an array of tuples, where we have the following inputs:

- `in`: a fixed length array of 100 tuples.
- `match`: an arbitrary input value.
And with the following outputs:
- `num_match`: the number of elements of `in` whose first entry matches `match`.
- `out`: whose first `num_match` entries are the tuples in `in` whose first entry agrees with `match`, with the remaining entries being 0-padded.

Where `n` is the number of tuples in the array.

## Naive Solution

A simple solution to the problem is to treat each task separately, and constrain the circuit accordingly as done in [`naive_solution.circom`](./naive_solution.circom). As such, first we will compute the value for `num_match` and later assign the values for `out`.

#### Computing the number of matches

To this end, we simply define `n` [`IsEqual`](https://github.com/iden3/circomlib/blob/master/circuits/comparators.circom#L37) components, comparing each first item of the tuple to the value `match` we are comparing against. We then just have to constrain `num_match` to equal the sum of the outputs of all these `IsEqual` components.

##### Assigning the output array

We will constrain the first item of the first `num_match` tuples of `out` to equal `match`, while the remaining ones we will enforce equal zero. We will then iterate through the array `n` times, each time selecting the second item of the `i`th tuple of `out` whose first item equals `match`. 

The resulting solution runs in $o(n²)$ time and uses 40,400 non linear constraints to be enforced. 
Open this in [zkREPL →](https://zkrepl.dev/?gist=0d1ef34486da201cde1358c9f248ba19)

## Optimized Solution

An [optimized solution](https://gist.github.com/axiomintern/ac214beea65dd6c5a1eaa2770493f48c) was provided by Axiom.

