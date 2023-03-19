include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell14qr.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cpellfund.mm"
include "cv.mm"
include "crab.mm"
include "cr.mm"
include "cinf.mm"
include "cle.mm"
include "wceq.mm"
include "pellfundval.mm"
include "3ad2ant1.mm"
include "wss.mm"
include "wral.mm"
include "wrex.mm"
include "ssrab2.mm"
include "pell14qrre.mm"
include "ex.mm"
include "ssrdv.mm"
include "syl5ss.mm"
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
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "simp2.mm"
include "simp3.mm"
include "sylanbrc.mm"
include "infrelb.mm"
include "syl3anc.mm"
include "eqbrtrd.mm"

theorem pellfundlb
  let cA: class A
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x


  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ 1 < A ) -> ( PellFund ` D ) <_ A )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cA
    cD
    cpell14qr
    cfv
    #
    wcel
    #
    c1
    cA
    clt
    wbr
    #
    w3a
    #
    cD
    cpellfund
    cfv
    #
    c1
    va
    cv
    #
    clt
    wbr
    #
    va
    @1
    crab
    #
    cr
    clt
    cinf
    #
    cA
    cle
    @0
    @2
    @5
    @9
    wceq
    @3
    va
    cD
    pellfundval
    3ad2ant1
    @4
    @8
    cr
    wss
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
    @8
    wral
    #
    vb
    cr
    wrex
    #
    cA
    @8
    wcel
    #
    @9
    cA
    cle
    wbr
    @0
    @2
    @10
    @3
    @0
    @8
    @1
    cr
    @7
    va
    @1
    ssrab2
    @0
    vd
    @1
    cr
    @0
    vd
    cv
    #
    @1
    wcel
    @17
    cr
    wcel
    @17
    cD
    pell14qrre
    ex
    ssrdv
    syl5ss
    3ad2ant1
    @4
    c1
    cr
    wcel
    #
    c1
    @12
    cle
    wbr
    #
    vc
    @8
    wral
    #
    @15
    1re
    @0
    @2
    @20
    @3
    @0
    @19
    vc
    @8
    @12
    @8
    wcel
    @12
    @1
    wcel
    #
    c1
    @12
    clt
    wbr
    #
    wa
    @0
    @19
    @7
    @22
    va
    @12
    @1
    @6
    @12
    c1
    clt
    breq2
    elrab
    @0
    @21
    @22
    @19
    @0
    @21
    wa
    @18
    @12
    cr
    wcel
    @22
    @19
    wi
    1re
    @12
    cD
    pell14qrre
    c1
    @12
    ltle
    sylancr
    expimpd
    syl5bi
    ralrimiv
    3ad2ant1
    @14
    @20
    vb
    c1
    cr
    @11
    c1
    wceq
    @13
    @19
    vc
    @8
    @11
    c1
    @12
    cle
    breq1
    ralbidv
    rspcev
    sylancr
    @4
    @2
    @3
    @16
    @0
    @2
    @3
    simp2
    @0
    @2
    @3
    simp3
    @7
    @3
    va
    cA
    @1
    @6
    cA
    c1
    clt
    breq2
    elrab
    sylanbrc
    vb
    vc
    cA
    @8
    infrelb
    syl3anc
    eqbrtrd
end
