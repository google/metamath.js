include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cpell14qr.mm"
include "crab.mm"
include "cr.mm"
include "cinf.mm"
include "cpellfund.mm"
include "cle.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "ssrab2.mm"
include "pell14qrre.mm"
include "ex.mm"
include "ssrdv.mm"
include "syl5ss.mm"
include "wrex.mm"
include "cpell1qr.mm"
include "pell1qrss14.mm"
include "pellqrex.mm"
include "ssrexv.mm"
include "sylc.mm"
include "rabn0.mm"
include "sylibr.mm"
include "eldifi.mm"
include "peano2nnd.mm"
include "nnrpd.mm"
include "rpsqrtcld.mm"
include "rpred.mm"
include "readdcld.mm"
include "wa.mm"
include "breq2.mm"
include "elrab.mm"
include "pell14qrgap.mm"
include "3expib.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "infmrgelbi.mm"
include "syl31anc.mm"
include "pellfundval.mm"
include "breqtrrd.mm"

theorem pellfundge
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cA: class A
  let vx: setvar x


  assert |- ( D e. ( NN \ []NN ) -> ( ( sqrt ` ( D + 1 ) ) + ( sqrt ` D ) ) <_ ( PellFund ` D ) )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cD
    c1
    caddc
    co
    #
    csqrt
    cfv
    #
    cD
    csqrt
    cfv
    #
    caddc
    co
    #
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
    cD
    cpellfund
    cfv
    cle
    @0
    @8
    cr
    wss
    @8
    c0
    wne
    #
    @4
    cr
    wcel
    @4
    vb
    cv
    #
    cle
    wbr
    #
    vb
    @8
    wral
    @4
    @9
    cle
    wbr
    @0
    @8
    @7
    cr
    @6
    va
    @7
    ssrab2
    @0
    va
    @7
    cr
    @0
    @5
    @7
    wcel
    @5
    cr
    wcel
    @5
    cD
    pell14qrre
    ex
    ssrdv
    syl5ss
    @0
    @6
    va
    @7
    wrex
    #
    @10
    @0
    cD
    cpell1qr
    cfv
    #
    @7
    wss
    @6
    va
    @14
    wrex
    @13
    cD
    pell1qrss14
    va
    cD
    pellqrex
    @6
    va
    @14
    @7
    ssrexv
    sylc
    @6
    va
    @7
    rabn0
    sylibr
    @0
    @2
    @3
    @0
    @2
    @0
    @1
    @0
    @1
    @0
    cD
    cD
    cn
    csquarenn
    eldifi
    #
    peano2nnd
    nnrpd
    rpsqrtcld
    rpred
    @0
    @3
    @0
    cD
    @0
    cD
    @15
    nnrpd
    rpsqrtcld
    rpred
    readdcld
    @0
    @12
    vb
    @8
    @11
    @8
    wcel
    @11
    @7
    wcel
    #
    c1
    @11
    clt
    wbr
    #
    wa
    @0
    @12
    @6
    @17
    va
    @11
    @7
    @5
    @11
    c1
    clt
    breq2
    elrab
    @0
    @16
    @17
    @12
    @11
    cD
    pell14qrgap
    3expib
    syl5bi
    ralrimiv
    vb
    @8
    @4
    infmrgelbi
    syl31anc
    va
    cD
    pellfundval
    breqtrrd
end
