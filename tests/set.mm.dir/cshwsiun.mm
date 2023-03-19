include "cword.mm"
include "wcel.mm"
include "cv.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "wrex.mm"
include "crab.mm"
include "csn.mm"
include "cab.mm"
include "ciun.mm"
include "wa.mm"
include "df-rab.mm"
include "eqcom.mm"
include "biimpi.mm"
include "reximi.mm"
include "adantl.mm"
include "cshwcl.mm"
include "adantr.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "imp.mm"
include "jca.mm"
include "ex.mm"
include "impbid2.mm"
include "wb.mm"
include "velsn.mm"
include "bicomi.mm"
include "a1i.mm"
include "rexbidv.mm"
include "bitrd.mm"
include "abbidv.mm"
include "syl5eq.mm"
include "df-iun.mm"
include "3eqtr4g.mm"

theorem cshwsiun
  let vw: setvar w
  let vn: setvar n
  let cM: class M
  let cV: class V
  let cW: class W
  assume cshwrepswhash1.m: |- M = { w e. Word V | E. n e. ( 0 ..^ ( # ` W ) ) ( W cyclShift n ) = w }

  disjoint V n
  disjoint V w
  disjoint n w
  disjoint W n
  disjoint W w
  assert |- ( W e. Word V -> M = U_ n e. ( 0 ..^ ( # ` W ) ) { ( W cyclShift n ) } )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cW
    vn
    cv
    #
    ccsh
    co
    #
    vw
    cv
    #
    wceq
    #
    vn
    cc0
    cW
    chash
    cfv
    cfzo
    co
    #
    wrex
    #
    vw
    @0
    crab
    #
    @4
    @3
    csn
    #
    wcel
    #
    vn
    @6
    wrex
    #
    vw
    cab
    #
    cM
    vn
    @6
    @9
    ciun
    @1
    @8
    @4
    @0
    wcel
    #
    @7
    wa
    #
    vw
    cab
    @12
    @7
    vw
    @0
    df-rab
    @1
    @14
    @11
    vw
    @1
    @14
    @4
    @3
    wceq
    #
    vn
    @6
    wrex
    #
    @11
    @1
    @14
    @16
    @7
    @16
    @13
    @5
    @15
    vn
    @6
    @5
    @15
    @3
    @4
    eqcom
    biimpi
    reximi
    adantl
    @1
    @16
    @14
    @1
    @16
    wa
    @13
    @7
    @1
    @16
    @13
    @1
    @15
    @13
    vn
    @6
    @1
    @2
    @6
    wcel
    #
    wa
    @13
    @15
    @3
    @0
    wcel
    #
    @1
    @18
    @17
    @2
    cV
    cW
    cshwcl
    adantr
    @4
    @3
    @0
    eleq1
    syl5ibrcom
    rexlimdva
    imp
    @16
    @7
    @1
    @15
    @5
    vn
    @6
    @15
    @5
    @4
    @3
    eqcom
    biimpi
    reximi
    adantl
    jca
    ex
    impbid2
    @1
    @15
    @10
    vn
    @6
    @15
    @10
    wb
    @1
    @10
    @15
    vw
    @3
    velsn
    bicomi
    a1i
    rexbidv
    bitrd
    abbidv
    syl5eq
    cshwrepswhash1.m
    vn
    vw
    @6
    @9
    df-iun
    3eqtr4g
end
