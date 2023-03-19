include "wer.mm"
include "crn.mm"
include "ccnv.mm"
include "cdm.mm"
include "df-rn.mm"
include "ercnv.mm"
include "dmeqd.mm"
include "erdm.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem errn
  let cA: class A
  let cR: class R


  assert |- ( R Er A -> ran R = A )

  proof
    cA
    cR
    wer
    #
    cR
    crn
    cR
    ccnv
    #
    cdm
    #
    cA
    cR
    df-rn
    @0
    @2
    cR
    cdm
    cA
    @0
    @1
    cR
    cA
    cR
    ercnv
    dmeqd
    cA
    cR
    erdm
    eqtrd
    syl5eq
end
