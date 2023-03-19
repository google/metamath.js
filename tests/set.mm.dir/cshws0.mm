include "c0.mm"
include "wceq.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "cv.mm"
include "ccsh.mm"
include "co.mm"
include "cfzo.mm"
include "wrex.mm"
include "cword.mm"
include "crab.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "0ex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "hasheq0.mm"
include "bicomd.mm"
include "syl.mm"
include "ibi.mm"
include "oveq2d.mm"
include "fzo0.mm"
include "syl6eq.mm"
include "rexeqdv.mm"
include "rabbidv.mm"
include "wn.mm"
include "wral.mm"
include "rex0.mm"
include "a1i.mm"
include "ralrimivw.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "hash0.mm"

theorem cshws0
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
  assert |- ( W = (/) -> ( # ` M ) = 0 )

  proof
    cW
    c0
    wceq
    #
    cM
    chash
    cfv
    c0
    chash
    cfv
    cc0
    @0
    cM
    c0
    chash
    @0
    cM
    cW
    vn
    cv
    ccsh
    co
    vw
    cv
    wceq
    #
    vn
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    wrex
    #
    vw
    cV
    cword
    #
    crab
    #
    c0
    cshwrepswhash1.m
    @0
    @6
    @1
    vn
    c0
    wrex
    #
    vw
    @5
    crab
    #
    c0
    @0
    @4
    @7
    vw
    @5
    @0
    @1
    vn
    @3
    c0
    @0
    @3
    cc0
    cc0
    cfzo
    co
    c0
    @0
    @2
    cc0
    cc0
    cfzo
    @0
    @2
    cc0
    wceq
    #
    @0
    cW
    cvv
    wcel
    #
    @0
    @9
    wb
    @0
    @10
    c0
    cvv
    wcel
    0ex
    cW
    c0
    cvv
    eleq1
    mpbiri
    @10
    @9
    @0
    cW
    cvv
    hasheq0
    bicomd
    syl
    ibi
    oveq2d
    cc0
    fzo0
    syl6eq
    rexeqdv
    rabbidv
    @0
    @7
    wn
    #
    vw
    @5
    wral
    @8
    c0
    wceq
    @0
    @11
    vw
    @5
    @11
    @0
    @1
    vn
    rex0
    a1i
    ralrimivw
    @7
    vw
    @5
    rabeq0
    sylibr
    eqtrd
    syl5eq
    fveq2d
    hash0
    syl6eq
end
