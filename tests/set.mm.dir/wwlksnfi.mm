include "cvv.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cvtx.mm"
include "cfv.mm"
include "cfn.mm"
include "cwwlksn.mm"
include "co.mm"
include "wi.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "cedg.mm"
include "cc0.mm"
include "chash.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "wceq.mm"
include "cword.mm"
include "crab.mm"
include "cwwlks.mm"
include "cab.mm"
include "wwlksn.mm"
include "df-rab.mm"
include "syl6eq.mm"
include "adantl.mm"
include "w3a.mm"
include "wb.mm"
include "eqid.mm"
include "iswwlks.mm"
include "a1i.mm"
include "anbi1d.mm"
include "abbidv.mm"
include "3anan12.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "abbii.mm"
include "eqtr4i.mm"
include "eqtrd.mm"
include "adantr.mm"
include "wss.mm"
include "peano2nn0.mm"
include "anim2i.mm"
include "ancoms.mm"
include "wrdnfi.mm"
include "syl.mm"
include "simpr.mm"
include "rgenw.mm"
include "ss2rab.mm"
include "mpbir.mm"
include "ssfi.mm"
include "sylancl.mm"
include "eqeltrd.mm"
include "ex.mm"
include "wn.mm"
include "wnel.mm"
include "wo.mm"
include "wwlksnndef.mm"
include "ioran.mm"
include "nnel.mm"
include "anbi12i.mm"
include "sylbb.mm"
include "nsyl4.mm"
include "0fin.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem wwlksnfi
  let cG: class G
  let cN: class N
  let vi: setvar i
  let vw: setvar w


  assert |- ( ( Vtx ` G ) e. Fin -> ( N WWalksN G ) e. Fin )

  proof
    cG
    cvv
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cG
    cvtx
    cfv
    #
    cfn
    wcel
    #
    cN
    cG
    cwwlksn
    co
    #
    cfn
    wcel
    #
    wi
    @2
    @4
    @6
    @2
    @4
    wa
    #
    @5
    vw
    cv
    #
    c0
    wne
    #
    vi
    cv
    #
    @8
    cfv
    @10
    c1
    caddc
    co
    @8
    cfv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    vi
    cc0
    @8
    chash
    cfv
    #
    c1
    cmin
    co
    cfzo
    co
    wral
    #
    wa
    #
    @12
    cN
    c1
    caddc
    co
    #
    wceq
    #
    wa
    #
    vw
    @3
    cword
    #
    crab
    #
    cfn
    @2
    @5
    @19
    wceq
    @4
    @2
    @5
    @8
    cG
    cwwlks
    cfv
    #
    wcel
    #
    @16
    wa
    #
    vw
    cab
    #
    @19
    @1
    @5
    @23
    wceq
    @0
    @1
    @5
    @16
    vw
    @20
    crab
    @23
    vw
    cG
    cN
    wwlksn
    @16
    vw
    @20
    df-rab
    syl6eq
    adantl
    @2
    @23
    @9
    @8
    @18
    wcel
    #
    @13
    w3a
    #
    @16
    wa
    #
    vw
    cab
    #
    @19
    @2
    @22
    @26
    vw
    @2
    @21
    @25
    @16
    @21
    @25
    wb
    @2
    vi
    @11
    cG
    @3
    @8
    @3
    eqid
    @11
    eqid
    iswwlks
    a1i
    anbi1d
    abbidv
    @27
    @24
    @17
    wa
    #
    vw
    cab
    @19
    @26
    @28
    vw
    @26
    @24
    @14
    wa
    #
    @16
    wa
    @28
    @25
    @29
    @16
    @9
    @24
    @13
    3anan12
    anbi1i
    @24
    @14
    @16
    anass
    bitri
    abbii
    @17
    vw
    @18
    df-rab
    eqtr4i
    syl6eq
    eqtrd
    adantr
    @7
    @16
    vw
    @18
    crab
    #
    cfn
    wcel
    #
    @19
    @30
    wss
    #
    @19
    cfn
    wcel
    @7
    @4
    @15
    cn0
    wcel
    #
    wa
    #
    @31
    @4
    @2
    @34
    @2
    @33
    @4
    @1
    @33
    @0
    cN
    peano2nn0
    adantl
    anim2i
    ancoms
    vw
    @15
    @3
    wrdnfi
    syl
    @32
    @17
    @16
    wi
    #
    vw
    @18
    wral
    @35
    vw
    @18
    @14
    @16
    simpr
    rgenw
    @17
    @16
    vw
    @18
    ss2rab
    mpbir
    @30
    @19
    ssfi
    sylancl
    eqeltrd
    ex
    @2
    wn
    #
    @6
    @4
    @36
    @5
    c0
    cfn
    cG
    cvv
    wnel
    #
    cN
    cn0
    wnel
    #
    wo
    #
    @5
    c0
    wceq
    @2
    cG
    cN
    wwlksnndef
    @39
    wn
    @37
    wn
    #
    @38
    wn
    #
    wa
    @2
    @37
    @38
    ioran
    @40
    @0
    @41
    @1
    cG
    cvv
    nnel
    cN
    cn0
    nnel
    anbi12i
    sylbb
    nsyl4
    c0
    cfn
    wcel
    @36
    0fin
    a1i
    eqeltrd
    a1d
    pm2.61i
end
