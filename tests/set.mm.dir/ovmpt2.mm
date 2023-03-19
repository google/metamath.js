include "wcel.mm"
include "cvv.mm"
include "co.mm"
include "wceq.mm"
include "ovmpt2g.mm"
include "mp3an3.mm"

theorem ovmpt2
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
  assume ovmpt2g.1: |- ( x = A -> R = G )
  assume ovmpt2g.2: |- ( y = B -> G = S )
  assume ovmpt2g.3: |- F = ( x e. C , y e. D |-> R )
  assume ovmpt2.4: |- S e. _V

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
  assert |- ( ( A e. C /\ B e. D ) -> ( A F B ) = S )

  proof
    cA
    cC
    wcel
    cB
    cD
    wcel
    cS
    cvv
    wcel
    cA
    cB
    cF
    co
    cS
    wceq
    ovmpt2.4
    vx
    vy
    cA
    cB
    cC
    cD
    cR
    cS
    cF
    cG
    cvv
    ovmpt2g.1
    ovmpt2g.2
    ovmpt2g.3
    ovmpt2g
    mp3an3
end
