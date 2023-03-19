include "wtru.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "tru.mm"
include "cv.mm"
include "adantl.mm"
include "caovclg.mm"
include "mpan.mm"

theorem caovcl
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  assume caovcl.1: |- ( ( x e. S /\ y e. S ) -> ( x F y ) e. S )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint S x
  disjoint S y
  assert |- ( ( A e. S /\ B e. S ) -> ( A F B ) e. S )

  proof
    wtru
    cA
    cS
    wcel
    cB
    cS
    wcel
    wa
    cA
    cB
    cF
    co
    cS
    wcel
    tru
    wtru
    vx
    vy
    cA
    cB
    cS
    cS
    cS
    cF
    vx
    cv
    #
    cS
    wcel
    vy
    cv
    #
    cS
    wcel
    wa
    @0
    @1
    cF
    co
    cS
    wcel
    wtru
    caovcl.1
    adantl
    caovclg
    mpan
end
