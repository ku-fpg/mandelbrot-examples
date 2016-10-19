% Walkthrough of the Accelerate Transformation

# Basic functions used in transformation

We essentially have

    abs :: a -> Exp a
    abs = lift

    rep :: Exp a -> a
    rep = error ...

There are some restrictions on the type of `abs` discussed [here](https://github.com/ku-fpg/mandelbrot-examples/wiki/Notes-on-Types-in-Accelerate).
Given above is the simplified version of the type of `abs`.

There is also `unlift`, which comes from the Accelerate library. This is a
limited, but "safe" version of `rep` (it can occur in the generated code without
causing a problem).

# Broad idea

`abs` and `rep` calls should be floated in. They can be cancelled with

    abs (rep x)  ==>  x

Some `rep`s can also be replaced with `unlift`s. No `rep`s can be left by the
time the transformation finishes (`abs`, however, is okay).


# Non-recursive transformations

## Part 1

The appropriate part of the program is targeted for transformation. In this
particular case, it looks for a call to `toRGBF`, which signifies the part of
the original program that interprets the result of the main computation as a
pixel color. An `abs` is introduced (and a `rep` as well, to allow the types to
line up). The `abs` is pushed deeper into the computation by the later
computations until it has reached all the "basic" nodes that need to be lifted.

The function arguments passed to the argument of `toRGBF` are ignored so that
dummy arguments can be passed in while keeping the types lined up. These two
dummy arguments are found and transformed in later stages.

    -- Given: dummyX, dummyY :: Exp Float
    -- and    const2 x _ _ = x
    toRGBF pointColor   ==>   toRGBF (const2 (rep (abs (pointColor (rep dummyX) (rep dummyY))))

Note that the use of `const2` so that no lambdas are introduced.

## Part 2

All basic operations get transformed. Some representative examples are

    forall a b
    a + b    ==>   rep (abs a + abs b)
    a >= b   ==>   rep (abs a >=* abs b)

## Part 3

`case` expressions are floated over `abs` calls:

    abs (case ... of x -> ...)
      ==>
    case ... of x -> abs (...)

This is repeatedly done while at the same time floating `let`s over `abs`:

    abs (let ... in ...)
      ==>
    let ... in abs (...)

During the `case` floating, care needs to be taken as some of these `case`s need
to be transformed into Accelerate `cond` calls (so they should not be not
floated). Right now, this is done manually. A general way to detect which sort
of transformation should be applied will need to be implemented at some point.


# Recursive transformations

In this section, parts marked with "(*)" are key to the recursion
transformation. The other parts are transformations that are specific to the
data types involved.

## Part 1 (*)

First, we use HERMIT's builtin `fix` introduction transformation:

    go = \arg -> ... go arg' ...
        ==>
    go = fix (\go' arg -> ... go' arg' ...)

We then inline `go` in the program body so that we have something of the form

    fix (...) a

Now we apply a transformation to float `abs` and `rep` into `fix`:

    abs (fix f a)
        ==>
    fix (\fRec -> intros (\x -> abs (f (rep . fRec) x))) a

The `intros` function here is just `id` with `NOINLINE` enabled. This is to
prevent a beta reduction from happening (should find a better name).

More simplification and careful `abs`-case floating occurs after that.

## Part 2 (*)

`cond`s are introduced here:

    abs (case b of True -> t; False -> f)
        ==>
    cond (abs b) (abs t) (abs f)

## Part 3 (*)

The `fix` is eliminated here, while marking the expression as recursive:

    -- Given: recursive, recCall with `id` types
    fix f arg
        ==>
    recursive (f (\x -> recCall (abs x)) arg)

`recursive` is the marker for a recursive expression while `recCall` is
substituted in every spot that the original function calls itself.

## Part 4

The original function in our example uses a triple as its argument. This is
transformed to a Accelerate triple here:

    recCall (abs (rep x, rep y, rep z))
        ==>
    recCall (lift (x, y, z))

## Part 5 (*)

The Accelerate `while` is introduced.

    -- Given the placeholder whileCond :: a -> Exp Bool 
    recursive (intros f x)
        ==>
    while whileCond (\__REC_ARG__ -> f (rep __REC_ARG__)) (abs x)

The name `__REC_ARG__` is matched on later in the transformation. Ideally, we
would be able to use a mangled name to avoid conflicts with user created
identifiers (maybe `MagicHash` would help to an extent?), but this works for the
time being.

## Part 6

Triples are transformed from `Exp (Float, Float, Float)` to `(Exp Float, Exp
Float, Exp Float)` for ease of use. This transformation can probably be made
simpler, so we won't go into the details here yet.

## Part 7 (*)

Conditional analysis starts to happen (to determine where the base case and
recursive cases are). Some of the specifics are not relevant to the general
ideas, so they will be omitted here.

There are placeholder functions

    recCondF, recCondT
      :: (Exp t -> Exp Bool) -> Exp Bool -> Exp t -> Exp t -> Exp t
    recCondF _ = cond
    recCondT _ = cond

These carry around a function representation of the `Exp Bool` argument to
`cond`. This function representation abstracts out the argument to the overall
recursive function as its argument. `recCondF` is used when the recursion
happens in the `False` branch and `recCondT` when it is in the `True` branch
(for this particular example, only `recCondF` is needed). Eventually a variant
will need to be created that is applied when both branches are recursive.

We use HERMIT's `abstract` transformation on `__REC_ARG__` at the `Exp Bool`
argument to `cond` calls so that we can have a function to grab for the above
placeholders:

    cond c t f  ==>   cond ((\__REC_ARG__ -> c) __REC_ARG__) t f

Now we can introduce the placeholders

    cond (c x) t f (recCall f)
        ==>
    recCondF (not . c) (c x) t (recCall f)

and likewise for `recCondT` (no `not` is needed there though).

## Part 8 (*)

These `cond` placeholders are moved up the cond chain, combining the conditional
function arguments with

    forall c x accCond c' t t' f'.
    cond (c x) t (recCondF accCond c' t' f')
        ==>
    recCondF (\arg -> not (c arg) &&* accCond arg)
             (c x)
             (cond c' t' f')



## Part 9 (*)

Eventually, this conditional function gets floated to the `while` and the lambda
needs to be eliminated. This is done in a similar way as the dummy argument
transformation in Part 1 of the non-recursive transformation.

We have `dummyArg :: a` and

    grabbedCond :: a -> b -> a
    grabbedCond = const
    {-# NOINLINE grabbedCond #-}

This allows

    while whileCond fn initial
        ==>
    while whileCond (grabbedCond fn (fn dummyArg)) i


## Part 10 (*)

Now this transformation can be applied and the `whileCond = error ...`
placeholder can be removed:

    forall accCond c t f initial.
    while whileCond (grabbedCond fn (recCondF accCond c' t f)) initial
        ==>
    fn (while accCond fn initial)

Note that `fn` is applied one more time. This is to handle the base case that
results from the `while` call.

## Part 11

We can eliminate `dummyX` and `dummyY` (TODO: Expand on this)

## Part 12 (*)

`recCall` is eliminated since it is no longer necessary

    recCall x   ==>   x

## Part 13

The final computation is lifted to an Accelerate-ready computation and the
Accelerate reference implementation is applied to it. (TODO: Expand on this)

