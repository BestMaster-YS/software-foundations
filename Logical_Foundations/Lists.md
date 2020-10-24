# Lists

## Pair of Numbers

```coq
Inductive natprod : Type :=
    | Pair (n1 n2 : nat).

Definition fst (n: natprod) :=
    match n with
    | Pair x y => x
    end.

Definition snd (n: natprod) :=
	match n with
	| Pair x y => y
end.
```

