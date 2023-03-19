include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpellfund.mm"
include "cfv.mm"
include "c1.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cpell14qr.mm"
include "crab.mm"
include "cr.mm"
include "cinf.mm"
include "pellfundval.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "wral.mm"
include "wrex.mm"
include "ssrab2.mm"
include "pell14qrre.mm"
include "ex.mm"
include "ssrdv.mm"
include "syl5ss.mm"
include "cpell1qr.mm"
include "pell1qrss14.mm"
include "pellqrex.mm"
include "ssrexv.mm"
include "sylc.mm"
include "rabn0.mm"
include "sylibr.mm"
include "1re.mm"
include "wa.mm"
include "breq2.mm"
include "elrab.mm"
include "wi.mm"
include "ltle.mm"
include "sylancr.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "wceq.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "infrecl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem pellfundre
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cA: class A
  let vx: setvar x


  assert |- ( D e. ( NN \ []NN ) -> ( PellFund ` D ) e. RR )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cD
    cpellfund
    cfv
    c1
    va
    cv
    #
    clt
    wbr
    #
    va
    cD
    cpell14qr
    cfv
    #
    crab
    #
    cr
    clt
    cinf
    #
    cr
    va
    cD
    pellfundval
    @0
    @4
    cr
    wss
    @4
    c0
    wne
    #
    vb
    cv
    #
    vc
    cv
    #
    cle
    wbr
    #
    vc
    @4
    wral
    #
    vb
    cr
    wrex
    #
    @5
    cr
    wcel
    @0
    @4
    @3
    cr
    @2
    va
    @3
    ssrab2
    @0
    va
    @3
    cr
    @0
    @1
    @3
    wcel
    @1
    cr
    wcel
    @1
    cD
    pell14qrre
    ex
    ssrdv
    syl5ss
    @0
    @2
    va
    @3
    wrex
    #
    @6
    @0
    cD
    cpell1qr
    cfv
    #
    @3
    wss
    @2
    va
    @13
    wrex
    @12
    cD
    pell1qrss14
    va
    cD
    pellqrex
    @2
    va
    @13
    @3
    ssrexv
    sylc
    @2
    va
    @3
    rabn0
    sylibr
    @0
    c1
    cr
    wcel
    #
    c1
    @8
    cle
    wbr
    #
    vc
    @4
    wral
    #
    @11
    1re
    @0
    @15
    vc
    @4
    @8
    @4
    wcel
    @8
    @3
    wcel
    #
    c1
    @8
    clt
    wbr
    #
    wa
    @0
    @15
    @2
    @18
    va
    @8
    @3
    @1
    @8
    c1
    clt
    breq2
    elrab
    @0
    @17
    @18
    @15
    @0
    @17
    wa
    @14
    @8
    cr
    wcel
    @18
    @15
    wi
    1re
    @8
    cD
    pell14qrre
    c1
    @8
    ltle
    sylancr
    expimpd
    syl5bi
    ralrimiv
    @10
    @16
    vb
    c1
    cr
    @7
    c1
    wceq
    @9
    @15
    vc
    @4
    @7
    c1
    @8
    cle
    breq1
    ralbidv
    rspcev
    sylancr
    vb
    vc
    @4
    infrecl
    syl3anc
    eqeltrd
end
