include "wcel.mm"
include "cvv.mm"
include "wral.mm"
include "elex.mm"
include "ralrimivw.mm"
include "syl.mm"
include "mpt2exxg.mm"
include "sylan2.mm"

theorem mpt2exg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  assume mpt2exg.1: |- F = ( x e. A , y e. B |-> C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint B x
  assert |- ( ( A e. R /\ B e. S ) -> F e. _V )

  proof
    cB
    cS
    wcel
    #
    cA
    cR
    wcel
    cB
    cvv
    wcel
    #
    vx
    cA
    wral
    #
    cF
    cvv
    wcel
    @0
    @1
    @2
    cB
    cS
    elex
    @1
    @1
    vx
    cA
    cB
    cvv
    elex
    ralrimivw
    syl
    vx
    vy
    cA
    cB
    cC
    cR
    cvv
    cF
    mpt2exg.1
    mpt2exxg
    sylan2
end
