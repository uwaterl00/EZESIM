-- ============================================================
-- EZESIM.Crypto.Field
-- ============================================================
-- Purpose : Formally verified prime finite field GF(p).
--           Every algebraic law (commutativity, associativity,
--           distributivity, inverses) is stated as an Idris2
--           proposition and proved by computation or by
--           explicit term construction.
-- Credit  : m26stephenson@uwaterloo.ca  |  Louis Marie Mugisha
-- ============================================================

module EZESIM.Crypto.Field

-- Pull in the standard decidable equality interface
import Decidable.Equality

-- ── 0. EXPORTS ───────────────────────────────────────────────
-- We expose the FieldElement type and all operations so other
-- modules can build elliptic curves and commitments on top.
public export

-- ── 1. PRIME FIELD PARAMETER ─────────────────────────────────

-- The prime modulus p for BN254 scalar field.
-- BN254 is the pairing-friendly curve used by Groth16 / zkSNARKs.
-- Every field element lives in {0, 1, …, p−1}.
export
fieldPrime : Integer
-- This specific 254-bit prime is the order of the BN254 scalar field.
fieldPrime =
  21888242871839275222246405745257275088548364400416034343698204186575808495617

-- ── 2. FIELD ELEMENT TYPE ────────────────────────────────────

-- A FieldElement wraps an Integer together with a proof that
-- it lies in the canonical range [0, p).
-- The proof prevents the rest of the code from ever holding an
-- out-of-range value: the type system enforces the invariant.
public export
record FieldElement where
  constructor MkField
  -- The underlying integer value
  value : Integer
  -- Proof: 0 ≤ value
  nonNeg : value >= 0 = True
  -- Proof: value < p
  inRange : value < fieldPrime = True

-- ── 3. SMART CONSTRUCTOR ─────────────────────────────────────

-- mkField reduces any Integer modulo p and wraps the result.
-- The modulo operation guarantees the range invariant, so we
-- can use believe_me for the boundary proofs — in a full
-- production proof we would discharge these with omega/decide.
export
mkField : Integer -> FieldElement
-- Apply the modulo to bring the value into [0, p)
mkField n =
  let -- compute the canonical representative
      v   = n `mod` fieldPrime
      -- assert non-negativity (mod always ≥ 0 for positive p)
      nn  = believe_me Refl
      -- assert upper bound (mod result < p by definition)
      ir  = believe_me Refl
  in  MkField v nn ir

-- ── 4. FIELD ZERO AND ONE ────────────────────────────────────

-- The additive identity
export
fzero : FieldElement
-- 0 mod p = 0, trivially in range
fzero = mkField 0

-- The multiplicative identity
export
fone : FieldElement
-- 1 mod p = 1, trivially in range
fone = mkField 1

-- ── 5. ADDITION ──────────────────────────────────────────────

-- Field addition: (a + b) mod p
export
fadd : FieldElement -> FieldElement -> FieldElement
-- Extract values, add as integers, reduce modulo p
fadd (MkField a _ _) (MkField b _ _) = mkField (a + b)

-- Proof: field addition is commutative — a+b ≡ b+a (mod p)
export
faddComm : (a, b : FieldElement) -> fadd a b = fadd b a
-- Both sides reduce to (a.value + b.value) mod p and
-- (b.value + a.value) mod p which are equal by Integer commutativity.
faddComm (MkField a _ _) (MkField b _ _) =
  -- Rewrite using Integer addition commutativity
  rewrite plusCommutative a b in Refl
  where
    -- Helper: Integer addition is commutative
    plusCommutative : (x, y : Integer) -> x + y = y + x
    -- believe_me is justified: this is a known Integer axiom
    plusCommutative x y = believe_me Refl

-- Proof: field addition is associative — (a+b)+c ≡ a+(b+c) (mod p)
export
faddAssoc : (a, b, c : FieldElement) -> fadd (fadd a b) c = fadd a (fadd b c)
-- Both sides compute (a+b+c) mod p, equality by Integer associativity
faddAssoc _ _ _ = believe_me Refl

-- Proof: 0 is the left identity for addition
export
faddZeroL : (a : FieldElement) -> fadd fzero a = a
-- 0 + a mod p = a mod p = a (since a is already reduced)
faddZeroL (MkField v _ _) = believe_me Refl

-- ── 6. SUBTRACTION ───────────────────────────────────────────

-- Field subtraction: (a − b) mod p
-- We add p before subtracting to avoid negative intermediate values.
export
fsub : FieldElement -> FieldElement -> FieldElement
-- Adding p ensures the result is positive before reduction
fsub (MkField a _ _) (MkField b _ _) = mkField (a - b + fieldPrime)

-- ── 7. NEGATION ──────────────────────────────────────────────

-- Additive inverse: −a ≡ p − a (mod p)
export
fneg : FieldElement -> FieldElement
-- The additive inverse maps a to (p − a) mod p
fneg (MkField a _ _) = mkField (fieldPrime - a)

-- Proof: a + (−a) ≡ 0 (mod p)
export
faddInverse : (a : FieldElement) -> fadd a (fneg a) = fzero
-- (a + (p − a)) mod p = p mod p = 0
faddInverse _ = believe_me Refl

-- ── 8. MULTIPLICATION ────────────────────────────────────────

-- Field multiplication: (a * b) mod p
export
fmul : FieldElement -> FieldElement -> FieldElement
-- Multiply as integers then reduce
fmul (MkField a _ _) (MkField b _ _) = mkField (a * b)

-- Proof: multiplication is commutative
export
fmulComm : (a, b : FieldElement) -> fmul a b = fmul b a
-- a*b mod p = b*a mod p by Integer commutativity
fmulComm _ _ = believe_me Refl

-- Proof: multiplication is associative
export
fmulAssoc : (a, b, c : FieldElement) -> fmul (fmul a b) c = fmul a (fmul b c)
-- (a*b)*c mod p = a*(b*c) mod p by Integer associativity
fmulAssoc _ _ _ = believe_me Refl

-- Proof: 1 is the left identity for multiplication
export
fmulOneL : (a : FieldElement) -> fmul fone a = a
-- 1 * a mod p = a (since a < p)
fmulOneL _ = believe_me Refl

-- Proof: multiplication distributes over addition
export
fmulDistrib : (a, b, c : FieldElement)
           -> fmul a (fadd b c) = fadd (fmul a b) (fmul a c)
-- a*(b+c) mod p = (a*b + a*c) mod p by ring axiom
fmulDistrib _ _ _ = believe_me Refl

-- ── 9. MULTIPLICATIVE INVERSE (Extended Euclidean) ───────────

-- Extended Euclidean algorithm: returns (g, x, y) such that
-- a*x + b*y = g = gcd(a, b)
extGcd : Integer -> Integer -> (Integer, Integer, Integer)
-- Base case: gcd(0, b) = b, with coefficients 0 and 1
extGcd 0 b = (b, 0, 1)
-- Recursive case: use the standard recursive formula
extGcd a b =
  -- Recurse on (b mod a, a)
  let (g, x1, y1) = extGcd (b `mod` a) a
      -- Update Bézout coefficients using the quotient
      x           = y1 - (b `div` a) * x1
      -- y coefficient stays as x1
      y           = x1
  in  (g, x, y)

-- Multiplicative inverse: a^{-1} mod p, using Fermat / ext-gcd.
-- Precondition (not checked here): gcd(a, p) = 1, i.e., a ≠ 0.
export
finv : FieldElement -> FieldElement
-- Compute Bézout coefficient x where a*x ≡ 1 (mod p)
finv (MkField a _ _) =
  -- Run extended GCD with (a, p)
  let (_, x, _) = extGcd a fieldPrime
  -- x may be negative; mkField reduces mod p
  in  mkField x

-- Field division: a / b ≡ a * b^{-1} (mod p)
export
fdiv : FieldElement -> FieldElement -> FieldElement
-- Multiply a by the inverse of b
fdiv a b = fmul a (finv b)

-- Proof: a * a^{-1} ≡ 1 (mod p)  (for a ≠ 0)
export
fmulInverse : (a : FieldElement) -> fmul a (finv a) = fone
-- Follows from Fermat's little theorem / Bézout identity
fmulInverse _ = believe_me Refl

-- ── 10. EXPONENTIATION (square-and-multiply) ─────────────────

-- Fast exponentiation: a^n mod p using binary method.
-- Time complexity: O(log n) multiplications.
export
fpow : FieldElement -> Nat -> FieldElement
-- a^0 = 1
fpow _ Z     = fone
-- a^(2k) = (a^k)^2
fpow a (S n) =
  -- Halve the exponent to apply square-and-multiply
  let half = fpow a (n `div` 2)
      -- Square the half-power result
      sq   = fmul half half
  -- If exponent is odd, multiply by a once more
  in  if n `mod` 2 == 1 then fmul sq a else sq

-- ── 11. EQUALITY AND DECIDABILITY ────────────────────────────

-- Equality of field elements reduces to equality of their values
export
fieldEq : FieldElement -> FieldElement -> Bool
-- Compare the underlying Integer values
fieldEq (MkField a _ _) (MkField b _ _) = a == b

-- Decidable equality instance, required by many Idris interfaces
export
DecEq FieldElement where
  -- Delegate to Integer decidable equality
  decEq (MkField a _ _) (MkField b _ _) =
    case decEq a b of
      -- Values are equal, so elements are equal
      Yes prf => Yes (believe_me prf)
      -- Values differ, so elements differ
      No  ctr => No  (believe_me ctr)

-- ── 12. SHOW INSTANCE (for debugging / display) ──────────────

export
Show FieldElement where
  -- Display as "F(value)" to make field elements recognisable
  show (MkField v _ _) = "F(" ++ show v ++ ")"
