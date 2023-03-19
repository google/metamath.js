include "wfun.mm"
include "wcel.mm"
include "w3a.mm"
include "crn.mm"
include "wnel.mm"
include "wa.mm"
include "csupp.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "cdm.mm"
include "crab.mm"
include "wceq.mm"
include "suppval1.mm"
include "adantr.mm"
include "wral.mm"
include "wn.mm"
include "df-nel.mm"
include "fvelrn.mm"
include "3ad2antl1.mm"
include "wb.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "syl5ibrcom.mm"
include "necon3bd.mm"
include "syl5bi.mm"
include "impancom.mm"
include "ralrimiv.mm"
include "rabid2.mm"
include "sylibr.mm"
include "eqtr4d.mm"

theorem suppdm
  let cF: class F
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vx: setvar x
  let vk: setvar k


  assert |- ( ( ( Fun F /\ F e. V /\ Z e. W ) /\ Z e/ ran F ) -> ( F supp Z ) = dom F )

  proof
    cF
    wfun
    #
    cF
    cV
    wcel
    #
    cZ
    cW
    wcel
    #
    w3a
    #
    cZ
    cF
    crn
    #
    wnel
    #
    wa
    #
    cF
    cZ
    csupp
    co
    #
    vx
    cv
    #
    cF
    cfv
    #
    cZ
    wne
    #
    vx
    cF
    cdm
    #
    crab
    #
    @11
    @3
    @7
    @12
    wceq
    @5
    vx
    cV
    cW
    cF
    cZ
    suppval1
    adantr
    @6
    @10
    vx
    @11
    wral
    @11
    @12
    wceq
    @6
    @10
    vx
    @11
    @3
    @8
    @11
    wcel
    #
    @5
    @10
    @5
    cZ
    @4
    wcel
    #
    wn
    @3
    @13
    wa
    #
    @10
    cZ
    @4
    df-nel
    @15
    @14
    @9
    cZ
    @15
    @14
    @9
    cZ
    wceq
    @9
    @4
    wcel
    #
    @0
    @1
    @13
    @16
    @2
    @8
    cF
    fvelrn
    3ad2antl1
    @14
    @16
    wb
    cZ
    @9
    cZ
    @9
    @4
    eleq1
    eqcoms
    syl5ibrcom
    necon3bd
    syl5bi
    impancom
    ralrimiv
    @10
    vx
    @11
    rabid2
    sylibr
    eqtr4d
end
