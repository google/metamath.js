include "cdm.mm"
include "ccnv.mm"
include "crn.mm"
include "cvv.mm"
include "cima.mm"
include "wcel.mm"
include "crab.mm"
include "dfdm4.mm"
include "dfrn4.mm"
include "mptpreima.mm"
include "3eqtri.mm"

theorem dmmpt
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y
  let cC: class C
  let cV: class V
  assume dmmpt.1: |- F = ( x e. A |-> B )


  assert |- dom F = { x e. A | B e. _V }

  proof
    cF
    cdm
    cF
    ccnv
    #
    crn
    @0
    cvv
    cima
    cB
    cvv
    wcel
    vx
    cA
    crab
    cF
    dfdm4
    @0
    dfrn4
    vx
    cA
    cB
    cvv
    cF
    dmmpt.1
    mptpreima
    3eqtri
end
