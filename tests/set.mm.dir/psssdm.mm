include "cps.mm"
include "wcel.mm"
include "wss.mm"
include "cxp.mm"
include "cin.mm"
include "cdm.mm"
include "psssdm2.mm"
include "wceq.mm"
include "sseqin2.mm"
include "biimpi.mm"
include "sylan9eq.mm"

theorem psssdm
  let cA: class A
  let cR: class R
  let cX: class X
  let vx: setvar x
  assume psssdm.1: |- X = dom R


  assert |- ( ( R e. PosetRel /\ A C_ X ) -> dom ( R i^i ( A X. A ) ) = A )

  proof
    cR
    cps
    wcel
    cA
    cX
    wss
    #
    cR
    cA
    cA
    cxp
    cin
    cdm
    cX
    cA
    cin
    #
    cA
    cA
    cR
    cX
    psssdm.1
    psssdm2
    @0
    @1
    cA
    wceq
    cA
    cX
    sseqin2
    biimpi
    sylan9eq
end
