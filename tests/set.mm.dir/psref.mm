include "cps.mm"
include "wcel.mm"
include "wbr.mm"
include "cuni.mm"
include "cdm.mm"
include "wceq.mm"
include "crn.mm"
include "psdmrn.mm"
include "simpld.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "wa.mm"
include "wi.mm"
include "pslem.mm"
include "simp2d.mm"
include "sylbid.mm"
include "imp.mm"

theorem psref
  let cA: class A
  let cR: class R
  let cX: class X
  assume psref.1: |- X = dom R


  assert |- ( ( R e. PosetRel /\ A e. X ) -> A R A )

  proof
    cR
    cps
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    cA
    cR
    wbr
    #
    @0
    @1
    cA
    cR
    cuni
    cuni
    #
    wcel
    #
    @2
    @0
    cX
    @3
    cA
    @0
    cX
    cR
    cdm
    #
    @3
    psref.1
    @0
    @5
    @3
    wceq
    cR
    crn
    @3
    wceq
    cR
    psdmrn
    simpld
    syl5eq
    eleq2d
    @0
    @2
    @2
    wa
    #
    @2
    wi
    @4
    @2
    wi
    @6
    cA
    cA
    wceq
    wi
    cA
    cA
    cA
    cR
    pslem
    simp2d
    sylbid
    imp
end
