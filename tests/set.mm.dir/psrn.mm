include "cps.mm"
include "wcel.mm"
include "cdm.mm"
include "crn.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "psdmrn.mm"
include "eqtr3.mm"
include "syl.mm"
include "syl5eq.mm"

theorem psrn
  let cR: class R
  let cX: class X
  assume psref.1: |- X = dom R


  assert |- ( R e. PosetRel -> X = ran R )

  proof
    cR
    cps
    wcel
    #
    cX
    cR
    cdm
    #
    cR
    crn
    #
    psref.1
    @0
    @1
    cR
    cuni
    cuni
    #
    wceq
    @2
    @3
    wceq
    wa
    @1
    @2
    wceq
    cR
    psdmrn
    @1
    @2
    @3
    eqtr3
    syl
    syl5eq
end
