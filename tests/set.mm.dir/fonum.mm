include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "wfo.mm"
include "cdom.mm"
include "wbr.mm"
include "fodomnum.mm"
include "imp.mm"
include "numdom.mm"
include "syldan.mm"

theorem fonum
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( A e. dom card /\ F : A -onto-> B ) -> B e. dom card )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    cA
    cB
    cF
    wfo
    #
    cB
    cA
    cdom
    wbr
    #
    cB
    @0
    wcel
    @1
    @2
    @3
    cA
    cB
    cF
    fodomnum
    imp
    cA
    cB
    numdom
    syldan
end
