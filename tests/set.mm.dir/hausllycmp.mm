include "cha.mm"
include "wcel.mm"
include "ccmp.mm"
include "wa.mm"
include "ctop.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "cnlly.mm"
include "haustop.mm"
include "adantr.mm"
include "ccl.mm"
include "wss.mm"
include "cuni.mm"
include "cdif.mm"
include "crab.mm"
include "eqid.mm"
include "simpll.mm"
include "difssd.mm"
include "ccld.mm"
include "simplr.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "opncld.mm"
include "syl2anc.mm"
include "cmpcld.mm"
include "simprr.mm"
include "wceq.mm"
include "elssuni.mm"
include "ad2antrl.mm"
include "dfss4.mm"
include "sylib.mm"
include "eleqtrrd.mm"
include "hauscmplem.mm"
include "sseq2d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "mpbid.mm"
include "simprrl.mm"
include "opnneip.mm"
include "syl3anc.mm"
include "sscls.mm"
include "clsss3.mm"
include "ssnei2.mm"
include "syl22anc.mm"
include "simprrr.mm"
include "vex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "elind.mm"
include "clscld.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "rspcev.mm"
include "rexlimddv.mm"
include "ralrimivva.mm"
include "isnlly.mm"
include "sylanbrc.mm"

theorem hausllycmp
  let cJ: class J
  let va: setvar a
  let vj: setvar j
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vs: setvar s
  let cA: class A
  let cV: class V
  let cX: class X


  assert |- ( ( J e. Haus /\ J e. Comp ) -> J e. N-Locally Comp )

  proof
    cJ
    cha
    wcel
    #
    cJ
    ccmp
    wcel
    #
    wa
    #
    cJ
    ctop
    wcel
    #
    cJ
    vv
    cv
    #
    crest
    co
    #
    ccmp
    wcel
    #
    vv
    vy
    cv
    #
    csn
    #
    cJ
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
    @10
    wral
    vx
    cJ
    wral
    cJ
    ccmp
    cnlly
    wcel
    @0
    @3
    @1
    cJ
    haustop
    #
    adantr
    @2
    @13
    vx
    vy
    cJ
    @10
    @2
    @10
    cJ
    wcel
    #
    @7
    @10
    wcel
    #
    wa
    #
    wa
    #
    @7
    vu
    cv
    #
    wcel
    #
    @19
    cJ
    ccl
    cfv
    #
    cfv
    #
    @10
    wss
    #
    wa
    #
    @13
    vu
    cJ
    @18
    @20
    @22
    cJ
    cuni
    #
    @25
    @10
    cdif
    #
    cdif
    #
    wss
    #
    wa
    #
    vu
    cJ
    wrex
    @24
    vu
    cJ
    wrex
    @18
    vz
    vu
    vv
    @7
    @26
    cJ
    @7
    @4
    wcel
    @4
    @21
    cfv
    @25
    vz
    cv
    cdif
    wss
    wa
    vv
    cJ
    wrex
    vz
    cJ
    crab
    #
    @25
    @25
    eqid
    #
    @30
    eqid
    @0
    @1
    @17
    simpll
    @18
    @25
    @10
    difssd
    @18
    @1
    @26
    cJ
    ccld
    cfv
    #
    wcel
    #
    cJ
    @26
    crest
    co
    ccmp
    wcel
    @0
    @1
    @17
    simplr
    #
    @18
    @3
    @15
    @33
    @0
    @3
    @1
    @17
    @14
    ad2antrr
    #
    @2
    @15
    @16
    simprl
    @10
    cJ
    @25
    @31
    opncld
    syl2anc
    @26
    cJ
    cmpcld
    syl2anc
    @18
    @7
    @10
    @27
    @2
    @15
    @16
    simprr
    @18
    @10
    @25
    wss
    #
    @27
    @10
    wceq
    @15
    @36
    @2
    @16
    @10
    cJ
    elssuni
    ad2antrl
    @10
    @25
    dfss4
    sylib
    #
    eleqtrrd
    hauscmplem
    @18
    @29
    @24
    vu
    cJ
    @18
    @28
    @23
    @20
    @18
    @27
    @10
    @22
    @37
    sseq2d
    anbi2d
    rexbidv
    mpbid
    @18
    @19
    cJ
    wcel
    #
    @24
    wa
    #
    wa
    #
    @22
    @12
    wcel
    cJ
    @22
    crest
    co
    #
    ccmp
    wcel
    #
    @13
    @40
    @9
    @11
    @22
    @40
    @3
    @19
    @9
    wcel
    #
    @19
    @22
    wss
    #
    @22
    @25
    wss
    #
    @22
    @9
    wcel
    @18
    @3
    @39
    @35
    adantr
    #
    @40
    @3
    @38
    @20
    @43
    @46
    @18
    @38
    @24
    simprl
    @18
    @38
    @20
    @23
    simprrl
    @7
    cJ
    @19
    opnneip
    syl3anc
    @40
    @3
    @19
    @25
    wss
    #
    @44
    @46
    @38
    @47
    @18
    @24
    @19
    cJ
    elssuni
    ad2antrl
    #
    @19
    cJ
    @25
    @31
    sscls
    syl2anc
    @40
    @3
    @47
    @45
    @46
    @48
    @19
    cJ
    @25
    @31
    clsss3
    syl2anc
    @8
    cJ
    @22
    @19
    @25
    @31
    ssnei2
    syl22anc
    @40
    @23
    @22
    @11
    wcel
    @18
    @38
    @20
    @23
    simprrr
    @22
    @10
    vx
    vex
    elpw2
    sylibr
    elind
    @40
    @1
    @22
    @32
    wcel
    #
    @42
    @18
    @1
    @39
    @34
    adantr
    @40
    @3
    @47
    @49
    @46
    @48
    @19
    cJ
    @25
    @31
    clscld
    syl2anc
    @22
    cJ
    cmpcld
    syl2anc
    @6
    @42
    vv
    @22
    @12
    @4
    @22
    wceq
    @5
    @41
    ccmp
    @4
    @22
    cJ
    crest
    oveq2
    eleq1d
    rspcev
    syl2anc
    rexlimddv
    ralrimivva
    vx
    vy
    vv
    ccmp
    cJ
    isnlly
    sylanbrc
end
