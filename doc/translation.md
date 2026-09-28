# Translation

We write ⟦`e`⟧Ξ to denote the translation of SimplicityHL expression `e` using environment Ξ from A.

The translation produces a Simplicity expression with source type A.

The target type depends on the SimplicityHL expression `e`.

## Unit literal

⟦`()`⟧Ξ = unit: A → 𝟙

## Product constructor

If Ctx(Ξ) ⊩ `b`: B

If Ctx(Ξ) ⊩ `c`: C

Then ⟦`(b, c)`⟧Ξ = pair ⟦`b`⟧Ξ ⟦`c`⟧Ξ: A → B × C

## Left constructor

If Ctx(Ξ) ⊩ `b`: B

Then ⟦`Left(b)`⟧Ξ = injl ⟦`b`⟧Ξ: A → B + C

For any C

## Right constructor

If Ctx(Ξ) ⊩ `c`: C

Then ⟦`Right(c)`⟧Ξ = injr ⟦`c`⟧Ξ: A → B + C

For any B

## Bit string literal

If `s` is a bit string of 2^n bits

Then ⟦`0bs`⟧Ξ = comp unit const 0bs: A → 𝟚^(2^n)

## Byte string literal

If `s` is a hex string of 2^n digits

Then ⟦`0xs`⟧Ξ = comp unit const 0xs: A → 𝟚^(4 * 2^n)

## Variable

If Ctx(Ξ)(`v`) = B

Then ⟦`v`⟧Ξ = Ξ(`v`): A → B

## Witness value

Ctx(Ξ) ⊩ `witness(name)`: B

Then ⟦`witness(name)`⟧Ξ = witness: A → B

## Jet

If `j` is the name of a jet of type B → C

If Ctx(Ξ) ⊩ `b`: B

Then ⟦`jet::j b`⟧Ξ = comp ⟦`b`⟧Ξ j: A → C

## Chaining

If Ctx(Ξ) ⊩ `b`: 𝟙

If Ctx(Ξ) ⊩ `c`: C

Then ⟦`b; c`⟧Ξ = comp (pair ⟦`b`⟧Ξ ⟦`c`⟧Ξ) (drop iden): A → C

## Let statement

If Ctx(Ξ) ⊩ `b`: B

If Product(PEnv(B, `p`), Ξ) ⊩ `c`: C

Then ⟦`let p: B = b; c`⟧Ξ = comp (pair ⟦`b`⟧Ξ iden) ⟦`c`⟧Product(PEnv(B, `p`), Ξ): A → C

## Match statement

If Ctx(Ξ) ⊩ `a`: B + C

If Product(PEnv(B, `x`), Ξ) ⊩ `b`: D

If Product(PEnv(C, `y`), Ξ) ⊩ `c`: D

Then ⟦`match a { Left(x) => b, Right(y) => c, }`⟧Ξ = comp (pair ⟦`a`⟧Ξ iden) (case ⟦`b`⟧Product(PEnv(B, `x`), Ξ) ⟦`c`⟧Product(PEnv(C, `y`), Ξ)): A → D

## Left unwrap

If Ctx(Ξ) ⊩ `b`: B + C

Then ⟦`b.unwrap_left()`⟧Ξ = comp (pair ⟦`b`⟧Ξ unit) (assertl iden #{fail 0}): A → B

## Right unwrap

If Ctx(Ξ) ⊩ `c`: B + C

Then ⟦`c.unwrap_right()`⟧Ξ = comp (pair ⟦`c`⟧Ξ unit) (assertr #{fail 0} iden): A → C

## Raw hash

If Ctx(Ξ) ⊩ `t`: T1 × ⋯ × Tn, where each Ti is as in the typing rule for raw hash

Here T1 × ⋯ × Tn is the balanced product that a tuple of n elements builds, so `(a, b, c)`: T1 × (T2 × T3) and `(a, b, c, d)`: (T1 × T2) × (T3 × T4)

Then ⟦`raw_hash::<(T1, …, Tn)>(t)`⟧Ξ = comp ⟦`t`⟧Ξ (comp (comp (pair (comp unit sha_256_ctx_8_init) iden) Add(T1 × ⋯ × Tn)) sha_256_ctx_8_finalize): A → 𝟚^256

where Add(T): Ctx8 × T → Ctx8 follows the balanced tree of the tuple:

Add(𝟙) = take iden

Add(𝟚^N) = sha_256_ctx_8_add_{N/8}

Add(L × R) = comp (pair (comp (pair (take iden) (drop (take iden))) Add(L)) (drop (drop iden))) Add(R)
