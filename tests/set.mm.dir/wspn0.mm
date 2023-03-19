include "c0.mm"
include "wceq.mm"
include "cwwspthsn.mm"
include "co.mm"
include "cv.mm"
include "cspths.mm"
include "cfv.mm"
include "wbr.mm"
include "wex.mm"
include "cwwlksn.mm"
include "crab.mm"
include "wspthsn.mm"
include "wn.mm"
include "wral.mm"
include "wcel.mm"
include "cn0.mm"
include "cvtx.mm"
include "cword.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "w3a.mm"
include "wi.mm"
include "wwlknbp1.mm"
include "eqeq1i.mm"
include "wrdeq.mm"
include "sylbi.mm"
include "eleq2d.mm"
include "0wrd0.mm"
include "syl6bb.mm"
include "wa.mm"
include "cc0.mm"
include "wb.mm"
include "fveq2.mm"
include "hash0.mm"
include "syl6eq.mm"
include "eqeq1d.mm"
include "adantl.mm"
include "wne.mm"
include "nn0p1gt0.mm"
include "gt0ne0d.mm"
include "eqneqall.mm"
include "eqcoms.mm"
include "syl5com.mm"
include "adantr.mm"
include "sylbid.mm"
include "expcom.mm"
include "com23.mm"
include "syl6bi.mm"
include "com14.mm"
include "3imp.mm"
include "syl.mm"
include "impcom.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "syl5eq.mm"

theorem wspn0
  let cG: class G
  let cN: class N
  let cV: class V
  let vf: setvar f
  let vw: setvar w
  assume wspn0.v: |- V = ( Vtx ` G )


  assert |- ( V = (/) -> ( N WSPathsN G ) = (/) )

  proof
    cV
    c0
    wceq
    #
    cN
    cG
    cwwspthsn
    co
    vf
    cv
    vw
    cv
    #
    cG
    cspths
    cfv
    wbr
    vf
    wex
    #
    vw
    cN
    cG
    cwwlksn
    co
    #
    crab
    #
    c0
    vw
    vf
    cG
    cN
    wspthsn
    @0
    @2
    wn
    #
    vw
    @3
    wral
    @4
    c0
    wceq
    @0
    @5
    vw
    @3
    @1
    @3
    wcel
    #
    @0
    @5
    @6
    cN
    cn0
    wcel
    #
    @1
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    @1
    chash
    cfv
    #
    cN
    c1
    caddc
    co
    #
    wceq
    #
    w3a
    @0
    @5
    wi
    #
    cG
    cN
    @1
    wwlknbp1
    @7
    @10
    @13
    @14
    @0
    @10
    @13
    @7
    @5
    @0
    @10
    @1
    c0
    wceq
    #
    @13
    @7
    @5
    wi
    wi
    @0
    @10
    @1
    c0
    cword
    #
    wcel
    @15
    @0
    @9
    @16
    @1
    @0
    @8
    c0
    wceq
    @9
    @16
    wceq
    cV
    @8
    c0
    wspn0.v
    eqeq1i
    @8
    c0
    wrdeq
    sylbi
    eleq2d
    @1
    0wrd0
    syl6bb
    @15
    @7
    @13
    @5
    @7
    @15
    @13
    @5
    wi
    @7
    @15
    wa
    @13
    cc0
    @12
    wceq
    #
    @5
    @15
    @13
    @17
    wb
    @7
    @15
    @11
    cc0
    @12
    @15
    @11
    c0
    chash
    cfv
    cc0
    @1
    c0
    chash
    fveq2
    hash0
    syl6eq
    eqeq1d
    adantl
    @7
    @17
    @5
    wi
    @15
    @7
    @12
    cc0
    wne
    #
    @17
    @5
    @7
    @12
    cN
    nn0p1gt0
    gt0ne0d
    @18
    @5
    wi
    @12
    cc0
    @5
    @12
    cc0
    eqneqall
    eqcoms
    syl5com
    adantr
    sylbid
    expcom
    com23
    syl6bi
    com14
    3imp
    syl
    impcom
    ralrimiva
    @2
    vw
    @3
    rabeq0
    sylibr
    syl5eq
end
