include "wcel.mm"
include "ccoss.mm"
include "cdm.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "eldmcoss.mm"
include "wa.mm"
include "wb.mm"
include "brcoss.mm"
include "anidms.mm"
include "pm4.24.mm"
include "exbii.mm"
include "syl6bbr.mm"
include "bitr4d.mm"

theorem eldmcoss2
  let cA: class A
  let cR: class R
  let cV: class V
  let vu: setvar u


  assert |- ( A e. V -> ( A e. dom ,~ R <-> A ,~ R A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cR
    ccoss
    #
    cdm
    wcel
    vu
    cv
    cA
    cR
    wbr
    #
    vu
    wex
    #
    cA
    cA
    @1
    wbr
    #
    vu
    cA
    cR
    cV
    eldmcoss
    @0
    @4
    @2
    @2
    wa
    #
    vu
    wex
    #
    @3
    @0
    @4
    @6
    wb
    vu
    cA
    cA
    cR
    cV
    cV
    brcoss
    anidms
    @2
    @5
    vu
    @2
    pm4.24
    exbii
    syl6bbr
    bitr4d
end
