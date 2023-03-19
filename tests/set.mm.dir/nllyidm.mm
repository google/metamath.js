include "cnlly.mm"
include "clly.mm"
include "cv.mm"
include "wcel.mm"
include "ctop.mm"
include "crest.mm"
include "co.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "llytop.mm"
include "wel.mm"
include "w3a.mm"
include "wss.mm"
include "llyi.mm"
include "wa.mm"
include "simprr3.mm"
include "simprl.mm"
include "ssid.mm"
include "a1i.mm"
include "wb.mm"
include "simpl1.mm"
include "syl.mm"
include "restopn2.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "simprr2.mm"
include "nlly2i.mm"
include "syl3anc.mm"
include "wi.mm"
include "adantr.mm"
include "cuni.mm"
include "simpr2l.mm"
include "simpr31.mm"
include "opnneip.mm"
include "simpr32.mm"
include "simpr1.mm"
include "elpwid.mm"
include "elssuni.mm"
include "sstrd.mm"
include "eqid.mm"
include "ssnei2.mm"
include "syl22anc.mm"
include "simprr1.mm"
include "selpw.mm"
include "sylibr.mm"
include "elind.mm"
include "wceq.mm"
include "restabs.mm"
include "simpr33.mm"
include "eqeltrrd.mm"
include "jca.mm"
include "3exp2.mm"
include "imp.mm"
include "sylbid.mm"
include "rexlimdv.mm"
include "expimpd.mm"
include "reximdv2.mm"
include "mpd.mm"
include "rexlimddv.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "isnlly.mm"
include "sylanbrc.mm"
include "ssriv.mm"
include "wtru.mm"
include "nllyrest.mm"
include "adantl.mm"
include "nllytop.mm"
include "restlly.mm"
include "trud.mm"
include "eqssi.mm"

theorem nllyidm
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


  assert |- Locally N-Locally A = N-Locally A

  proof
    cA
    cnlly
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
    vv
    vy
    cv
    #
    csn
    #
    @2
    cnei
    cfv
    cfv
    #
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
    @11
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
    @14
    vx
    vy
    @2
    @11
    @3
    vx
    vj
    wel
    #
    vy
    vx
    wel
    #
    @14
    @3
    @17
    @18
    w3a
    #
    vu
    cv
    #
    @11
    wss
    #
    vy
    vu
    wel
    #
    @2
    @20
    crest
    co
    #
    @0
    wcel
    #
    w3a
    #
    @14
    vu
    @2
    vu
    @0
    @8
    @11
    @2
    llyi
    @19
    vu
    vj
    wel
    #
    @25
    wa
    #
    wa
    #
    vy
    vz
    wel
    #
    vz
    cv
    #
    @5
    wss
    #
    @23
    @5
    crest
    co
    #
    cA
    wcel
    #
    w3a
    #
    vz
    @23
    wrex
    #
    vv
    @20
    cpw
    #
    wrex
    #
    @14
    @28
    @24
    @20
    @23
    wcel
    #
    @22
    @37
    @21
    @22
    @24
    @26
    @19
    simprr3
    @28
    @38
    @26
    @20
    @20
    wss
    #
    @19
    @26
    @25
    simprl
    #
    @39
    @28
    @20
    ssid
    a1i
    @28
    @4
    @26
    @38
    @26
    @39
    wa
    wb
    @28
    @3
    @4
    @3
    @17
    @18
    @27
    simpl1
    @16
    syl
    #
    @40
    @20
    @20
    @2
    restopn2
    syl2anc
    mpbir2and
    @21
    @22
    @24
    @26
    @19
    simprr2
    vz
    cA
    @8
    @20
    @23
    vv
    nlly2i
    syl3anc
    @28
    @35
    @7
    vv
    @36
    @13
    @28
    @5
    @36
    wcel
    #
    @35
    @5
    @13
    wcel
    #
    @7
    wa
    #
    @28
    @42
    wa
    #
    @34
    @44
    vz
    @23
    @45
    @30
    @23
    wcel
    #
    vz
    vj
    wel
    #
    @30
    @20
    wss
    #
    wa
    #
    @34
    @44
    wi
    #
    @28
    @46
    @49
    wb
    #
    @42
    @28
    @4
    @26
    @51
    @41
    @40
    @20
    @30
    @2
    restopn2
    syl2anc
    adantr
    @28
    @42
    @49
    @50
    wi
    @28
    @42
    @49
    @34
    @44
    @28
    @42
    @49
    @34
    w3a
    #
    wa
    #
    @43
    @7
    @53
    @10
    @12
    @5
    @53
    @4
    @30
    @10
    wcel
    #
    @31
    @5
    @2
    cuni
    #
    wss
    @5
    @10
    wcel
    @28
    @4
    @52
    @41
    adantr
    #
    @53
    @4
    @47
    @29
    @54
    @56
    @47
    @48
    @42
    @34
    @28
    simpr2l
    @29
    @31
    @33
    @42
    @49
    @28
    simpr31
    @8
    @2
    @30
    opnneip
    syl3anc
    @29
    @31
    @33
    @42
    @49
    @28
    simpr32
    @53
    @5
    @20
    @55
    @53
    @5
    @20
    @28
    @42
    @49
    @34
    simpr1
    elpwid
    #
    @53
    @26
    @20
    @55
    wss
    @28
    @26
    @52
    @40
    adantr
    #
    @20
    @2
    elssuni
    syl
    sstrd
    @9
    @2
    @5
    @30
    @55
    @55
    eqid
    ssnei2
    syl22anc
    @53
    @5
    @11
    wss
    @5
    @12
    wcel
    @53
    @5
    @20
    @11
    @57
    @28
    @21
    @52
    @21
    @22
    @24
    @26
    @19
    simprr1
    adantr
    sstrd
    vv
    @11
    selpw
    sylibr
    elind
    @53
    @32
    @6
    cA
    @53
    @4
    @5
    @20
    wss
    @26
    @32
    @6
    wceq
    @56
    @57
    @58
    @5
    @20
    @2
    ctop
    @2
    restabs
    syl3anc
    @29
    @31
    @33
    @42
    @49
    @28
    simpr33
    eqeltrrd
    jca
    3exp2
    imp
    sylbid
    rexlimdv
    expimpd
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
    isnlly
    sylanbrc
    ssriv
    @0
    @1
    wss
    wtru
    vx
    @0
    vj
    @15
    @17
    wa
    @2
    @11
    crest
    co
    @0
    wcel
    wtru
    cA
    @11
    @2
    nllyrest
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
    nllytop
    ssriv
    a1i
    restlly
    trud
    eqssi
end
