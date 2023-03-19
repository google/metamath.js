include "clly.mm"
include "cv.mm"
include "wcel.mm"
include "ctop.mm"
include "wel.mm"
include "crest.mm"
include "co.mm"
include "wa.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "llytop.mm"
include "w3a.mm"
include "wss.mm"
include "llyi.mm"
include "simprr3.mm"
include "simprl.mm"
include "ssid.mm"
include "a1i.mm"
include "wb.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "restopn2.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "simprr2.mm"
include "syl3anc.mm"
include "simpl.mm"
include "syl6bi.mm"
include "simprr1.mm"
include "sstrd.mm"
include "selpw.mm"
include "sylibr.mm"
include "elind.mm"
include "wceq.mm"
include "simplrl.mm"
include "restabs.mm"
include "eqeltrrd.mm"
include "jca32.mm"
include "ex.mm"
include "syland.mm"
include "reximdv2.mm"
include "mpd.mm"
include "rexlimddv.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "islly.mm"
include "sylanbrc.mm"
include "ssriv.mm"
include "wtru.mm"
include "llyrest.mm"
include "adantl.mm"
include "restlly.mm"
include "trud.mm"
include "eqssi.mm"

theorem llyidm
  let cA: class A
  let vj: setvar j
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cJ: class J


  assert |- Locally Locally A = Locally A

  proof
    cA
    clly
    #
    clly
    #
    @0
    vj
    @1
    @0
    vj
    cv
    #
    @1
    wcel
    #
    @2
    ctop
    wcel
    #
    vy
    vv
    wel
    #
    @2
    vv
    cv
    #
    crest
    co
    #
    cA
    wcel
    #
    wa
    #
    vv
    @2
    vx
    cv
    #
    cpw
    #
    cin
    #
    wrex
    #
    vy
    @10
    wral
    vx
    @2
    wral
    @2
    @0
    wcel
    #
    @0
    @2
    llytop
    #
    @3
    @13
    vx
    vy
    @2
    @10
    @3
    vx
    vj
    wel
    #
    vy
    vx
    wel
    #
    @13
    @3
    @16
    @17
    w3a
    #
    vu
    cv
    #
    @10
    wss
    #
    vy
    vu
    wel
    #
    @2
    @19
    crest
    co
    #
    @0
    wcel
    #
    w3a
    #
    @13
    vu
    @2
    vu
    @0
    vy
    cv
    #
    @10
    @2
    llyi
    @18
    vu
    vj
    wel
    #
    @24
    wa
    #
    wa
    #
    @6
    @19
    wss
    #
    @5
    @22
    @6
    crest
    co
    #
    cA
    wcel
    #
    w3a
    #
    vv
    @22
    wrex
    #
    @13
    @28
    @23
    @19
    @22
    wcel
    #
    @21
    @33
    @20
    @21
    @23
    @26
    @18
    simprr3
    @28
    @34
    @26
    @19
    @19
    wss
    #
    @18
    @26
    @24
    simprl
    #
    @35
    @28
    @19
    ssid
    a1i
    @28
    @4
    @26
    @34
    @26
    @35
    wa
    wb
    @18
    @4
    @27
    @3
    @16
    @4
    @17
    @15
    3ad2ant1
    adantr
    #
    @36
    @19
    @19
    @2
    restopn2
    syl2anc
    mpbir2and
    @20
    @21
    @23
    @26
    @18
    simprr2
    vv
    cA
    @25
    @19
    @22
    llyi
    syl3anc
    @28
    @32
    @9
    vv
    @22
    @12
    @28
    @6
    @22
    wcel
    #
    vv
    vj
    wel
    #
    @32
    @6
    @12
    wcel
    #
    @9
    wa
    #
    @28
    @38
    @39
    @29
    wa
    #
    @39
    @28
    @4
    @26
    @38
    @42
    wb
    @37
    @36
    @19
    @6
    @2
    restopn2
    syl2anc
    @39
    @29
    simpl
    syl6bi
    @28
    @39
    @32
    wa
    #
    @41
    @28
    @43
    wa
    #
    @40
    @5
    @8
    @44
    @2
    @11
    @6
    @28
    @39
    @32
    simprl
    @44
    @6
    @10
    wss
    @6
    @11
    wcel
    @44
    @6
    @19
    @10
    @29
    @5
    @31
    @39
    @28
    simprr1
    #
    @28
    @20
    @43
    @20
    @21
    @23
    @26
    @18
    simprr1
    adantr
    sstrd
    vv
    @10
    selpw
    sylibr
    elind
    @29
    @5
    @31
    @39
    @28
    simprr2
    @44
    @30
    @7
    cA
    @44
    @4
    @29
    @26
    @30
    @7
    wceq
    @28
    @4
    @43
    @37
    adantr
    @45
    @18
    @26
    @24
    @43
    simplrl
    @6
    @19
    @2
    ctop
    @2
    restabs
    syl3anc
    @29
    @5
    @31
    @39
    @28
    simprr3
    eqeltrrd
    jca32
    ex
    syland
    reximdv2
    mpd
    rexlimddv
    3expb
    ralrimivva
    vx
    vy
    vv
    cA
    @2
    islly
    sylanbrc
    ssriv
    @0
    @1
    wss
    wtru
    vx
    @0
    vj
    @14
    @16
    wa
    @2
    @10
    crest
    co
    @0
    wcel
    wtru
    cA
    @10
    @2
    llyrest
    adantl
    @0
    ctop
    wss
    wtru
    vj
    @0
    ctop
    cA
    @2
    llytop
    ssriv
    a1i
    restlly
    trud
    eqssi
end
