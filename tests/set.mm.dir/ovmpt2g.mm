include "cv.mm"
include "wceq.mm"
include "sylan9eq.mm"
include "ovmpt2ga.mm"

theorem ovmpt2g
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  assume ovmpt2g.1: |- ( x = A -> R = G )
  assume ovmpt2g.2: |- ( y = B -> G = S )
  assume ovmpt2g.3: |- F = ( x e. C , y e. D |-> R )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint S x
  disjoint S y
  assert |- ( ( A e. C /\ B e. D /\ S e. H ) -> ( A F B ) = S )

  proof
    vx
    vy
    cA
    cB
    cC
    cD
    cR
    cS
    cF
    cH
    vx
    cv
    cA
    wceq
    vy
    cv
    cB
    wceq
    cR
    cG
    cS
    ovmpt2g.1
    ovmpt2g.2
    sylan9eq
    ovmpt2g.3
    ovmpt2ga
end
