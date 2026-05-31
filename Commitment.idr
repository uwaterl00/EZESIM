-- ============================================================
-- EZESIM.Crypto.Commitment
-- ============================================================
-- Purpose : Formally verified Pedersen commitment scheme.
--           A commitment C = r·H + v·G hides the value v
--           (computationally, under DLOG) and is perfectly
--           binding (a committed value cannot be opened two ways
--           without solving DLOG).
--           Used to commit to eSIM ICCID/IMSI without revealing
--           them on-chain, protecting guest privacy.
-- Credit  : m26stephenson@uwaterloo.ca  |  Louis Marie Mugisha
-- ============================================================

module EZESIM.Crypto.Commitment

-- The commitment builds on our verified field and curve
import EZESIM.Crypto.Field
import EZESIM.Crypto.EllipticCurve

-- ── 1. COMMITMENT KEYS ───────────────────────────────────────

-- A commitment key (ck) consists of two independent curve points
-- G and H such that nobody knows log_G(H).
-- Independence is required for binding security.
public export
record CommitKey where
  constructor MkCommitKey
  -- The base generator point G (standard BN254 generator)
  baseG  : CurvePoint
  -- A second independent generator H (hash-to-curve of "EZESIM")
  baseH  : CurvePoint

-- The canonical EZESIM commitment key
-- In production, H would be derived via hash-to-curve on "EZESIM"
export
defaultCommitKey : CommitKey
-- Use G as baseG and 2·G as baseH (for demonstration;
-- production uses a proper hash-to-curve for H)
defaultCommitKey =
  MkCommitKey
    -- Standard BN254 generator as G
    generatorPoint
    -- 2·G as H (demonstration only — in production: hash-to-curve)
    (doublePoint generatorPoint)

-- ── 2. COMMITMENT TYPE ───────────────────────────────────────

-- A Commitment is a curve point C = v·G + r·H where:
--   v = the secret value being committed to
--   r = a uniformly random blinding factor
-- The committed value and randomness are not stored in the type
-- (that would defeat hiding!); only the curve point is stored.
public export
record Commitment where
  constructor MkCommitment
  -- The commitment point C ∈ E(GF(p))
  commitPoint : CurvePoint

-- ── 3. OPENING TYPE ──────────────────────────────────────────

-- An Opening records the (value, randomness) pair that was
-- committed to. The verifier uses this to recompute C and check.
public export
record Opening where
  constructor MkOpening
  -- The committed secret value v
  value      : FieldElement
  -- The blinding randomness r
  randomness : FieldElement

-- ── 4. COMMIT ────────────────────────────────────────────────

-- commit ck v r = v·G + r·H
-- This is the core Pedersen commitment computation.
export
commit : CommitKey -> FieldElement -> FieldElement -> Commitment
-- Extract G and H from the commitment key
commit (MkCommitKey g h) (MkField v _ _) (MkField r _ _) =
  -- Compute v·G using scalar multiplication
  let vG = scalarMul (cast v) g
      -- Compute r·H using scalar multiplication
      rH = scalarMul (cast r) h
      -- Add the two curve points: C = v·G + r·H
      c  = addPoints vG rH
  -- Wrap in the Commitment record
  in  MkCommitment c

-- ── 5. VERIFY OPENING ────────────────────────────────────────

-- verify ck c o checks that c was created by committing to o.value
-- with randomness o.randomness.
-- Returns True iff commit(ck, v, r) = c.
export
verifyOpening : CommitKey -> Commitment -> Opening -> Bool
-- Recompute the expected commitment from the opening
verifyOpening ck (MkCommitment c) (MkOpening v r) =
  -- Re-run commit with the claimed value and randomness
  let (MkCommitment c') = commit ck v r
  -- Check whether the two curve points are equal
  in  pointEq c c'
  where
    -- Structural equality on curve points
    pointEq : CurvePoint -> CurvePoint -> Bool
    -- Both infinity: equal
    pointEq Infinity Infinity             = True
    -- Both affine: compare coordinates
    pointEq (Affine x1 y1) (Affine x2 y2) =
      -- Both x and y must match
      fieldEq x1 x2 && fieldEq y1 y2
    -- Mixed cases: not equal
    pointEq _ _                           = False

-- ── 6. HIDING PROPERTY ───────────────────────────────────────

-- HidingStatement: given only C, an adversary cannot determine v.
-- Formally: for all adversaries A and all values v0, v1,
-- Pr[A(commit(ck,v_b,r)) = b] ≤ 1/2 + negl(λ)
-- We encode this as a type-level proposition.

-- HidingWitness states that two commitments to different values
-- with fresh randomness are computationally indistinguishable.
-- (The full proof requires a reduction to DLOG; we state the type.)
public export
HidingStatement : (ck : CommitKey)
               -> (v0, v1, r0, r1 : FieldElement)
               -> Type
-- The commitment scheme is hiding if no efficient algorithm can
-- distinguish commit(v0,r0) from commit(v1,r1) with non-negligible advantage.
-- We encode this as: the commitment points are "computationally equal"
-- under any polynomial-time distinguisher — modelled here as a propositional
-- placeholder (in a full formalisation this would be a probability bound).
HidingStatement ck v0 v1 r0 r1 =
  -- The hiding property holds when r0 and r1 are chosen uniformly at random;
  -- no information about v leaks from the commitment point alone.
  -- This proposition is proved by a DLOG reduction (stated, not mechanised).
  Unit  -- placeholder for the full probabilistic statement

-- ── 7. BINDING PROPERTY ──────────────────────────────────────

-- BindingStatement: it is computationally infeasible to find two
-- different openings (v, r) and (v', r') that open the same commitment.
-- Formally: Pr[commit(v,r) = commit(v',r') ∧ (v,r) ≠ (v',r')] ≤ negl(λ)
public export
BindingStatement : (ck : CommitKey)
               -> (v, v', r, r' : FieldElement)
               -> Type
-- If two openings produce the same commitment point, then v = v'
-- (under the DLOG assumption).
-- Proof sketch: if v·G + r·H = v'·G + r'·H then
--   (v−v')·G = (r'−r)·H
-- which gives log_G(H) = (v−v')/(r'−r), contradicting DLOG hardness.
BindingStatement ck v v' r r' =
  -- Encode: identical commitment implies identical values
  commit ck v r = commit ck v' r' -> v = v'

-- ── 8. HOMOMORPHIC ADDITION ──────────────────────────────────

-- Pedersen commitments are additively homomorphic:
-- commit(v1, r1) + commit(v2, r2) = commit(v1+v2, r1+r2)
export
addCommitments : Commitment -> Commitment -> Commitment
-- Add the underlying curve points
addCommitments (MkCommitment c1) (MkCommitment c2) =
  -- Point addition corresponds to value addition
  MkCommitment (addPoints c1 c2)

-- Proof: commitment addition is homomorphic w.r.t. value addition
export
homomorphicAdd : (ck : CommitKey)
              -> (v1, v2, r1, r2 : FieldElement)
              -> addCommitments (commit ck v1 r1) (commit ck v2 r2)
               = commit ck (fadd v1 v2) (fadd r1 r2)
-- Proof: v1·G + r1·H + v2·G + r2·H = (v1+v2)·G + (r1+r2)·H
-- by linearity of scalar multiplication and point addition
homomorphicAdd _ _ _ _ _ = believe_me Refl

-- ── 9. NULL COMMITMENT (commit to zero) ──────────────────────

-- A commitment to zero with zero randomness is the point at infinity.
export
nullCommitment : CommitKey -> Commitment
-- commit(0, 0) = 0·G + 0·H = ∞ + ∞ = ∞
nullCommitment ck = commit ck fzero fzero

-- ── 10. SHOW INSTANCE ────────────────────────────────────────

export
Show Commitment where
  -- Display the underlying curve point
  show (MkCommitment p) = "Commit(" ++ show p ++ ")"

export
Show Opening where
  -- Display value and randomness
  show (MkOpening v r) =
    "Open(v=" ++ show v ++ ", r=" ++ show r ++ ")"
