include "wfo.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "wacn.mm"
include "cdom.mm"
include "wbr.mm"
include "cvv.mm"
include "fornex.mm"
include "com12.mm"
include "numacn.mm"
include "syli.mm"
include "fodomacn.mm"

theorem fodomnum
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( A e. dom card -> ( F : A -onto-> B -> B ~<_ A ) )

  proof
    cA
    cB
    cF
    wfo
    #
    cA
    ccrd
    cdm
    #
    wcel
    #
    cA
    cB
    wacn
    wcel
    #
    cB
    cA
    cdom
    wbr
    @0
    @2
    @3
    @2
    @0
    cB
    cvv
    wcel
    #
    @3
    @2
    @0
    @4
    cA
    cB
    @1
    cF
    fornex
    com12
    cB
    cvv
    cA
    numacn
    syli
    com12
    cA
    cB
    cF
    fodomacn
    syli
end
