include "wcel.mm"
include "cvv.mm"
include "co.mm"
include "wceq.mm"
include "ovmpt2ga.mm"
include "mp3an3.mm"

theorem ovmpt2a
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  assume ovmpt2ga.1: |- ( ( x = A /\ y = B ) -> R = S )
  assume ovmpt2ga.2: |- F = ( x e. C , y e. D |-> R )
  assume ovmpt2a.4: |- S e. _V

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
    ovmpt2a.4
    vx
    vy
    cA
    cB
    cC
    cD
    cR
    cS
    cF
    cvv
    ovmpt2ga.1
    ovmpt2ga.2
    ovmpt2ga
    mp3an3
end
