include "ccmp.mm"
include "cnlly.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "ctop.mm"
include "cv.mm"
include "csn.mm"
include "cnei.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "nllytop.mm"
include "resttop.mm"
include "sylan.mm"
include "wceq.mm"
include "elrest.mm"
include "wss.mm"
include "w3a.mm"
include "simpll.mm"
include "simprl.mm"
include "inss1.mm"
include "simprr.mm"
include "sseldi.mm"
include "nlly2i.mm"
include "syl3anc.mm"
include "cuni.mm"
include "ad2antrr.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "simprlr.mm"
include "elrestr.mm"
include "simprr1.mm"
include "inss2.mm"
include "simplrr.mm"
include "elind.mm"
include "opnneip.mm"
include "simprr2.mm"
include "ssrin.mm"
include "syl.mm"
include "eqid.mm"
include "cldss.mm"
include "restuni.mm"
include "syl2anc.mm"
include "syl5sseq.mm"
include "ssnei2.mm"
include "syl22anc.mm"
include "simprll.mm"
include "elpwid.mm"
include "vex.mm"
include "inex1.mm"
include "elpw.mm"
include "sylibr.mm"
include "a1i.mm"
include "restabs.mm"
include "eqtr4d.mm"
include "simprr3.mm"
include "incom.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "wb.mm"
include "simplrl.mm"
include "elssuni.mm"
include "sstrd.mm"
include "restcld.mm"
include "mpbird.mm"
include "syl5eqel.mm"
include "cmpcld.mm"
include "eqeltrd.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "pweq.mm"
include "ineq2d.mm"
include "rexeqdv.mm"
include "raleqbi1dv.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "isnlly.mm"
include "sylanbrc.mm"

theorem cldllycmp
  let cA: class A
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
  let cV: class V
  let cX: class X


  assert |- ( ( J e. N-Locally Comp /\ A e. ( Clsd ` J ) ) -> ( J |`t A ) e. N-Locally Comp )

  proof
    cJ
    ccmp
    cnlly
    #
    wcel
    #
    cA
    cJ
    ccld
    cfv
    #
    wcel
    #
    wa
    #
    cJ
    cA
    crest
    co
    #
    ctop
    wcel
    #
    @5
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
    @5
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
    @13
    wral
    #
    vx
    @5
    wral
    @5
    @0
    wcel
    @1
    cJ
    ctop
    wcel
    #
    @3
    @6
    ccmp
    cJ
    nllytop
    #
    cA
    cJ
    @2
    resttop
    sylan
    #
    @4
    @17
    vx
    @5
    @4
    @13
    @5
    wcel
    @13
    vu
    cv
    #
    cA
    cin
    #
    wceq
    #
    vu
    cJ
    wrex
    @17
    vu
    @13
    cA
    cJ
    @0
    @2
    elrest
    @4
    @23
    @17
    vu
    cJ
    @4
    @21
    cJ
    wcel
    #
    wa
    #
    @17
    @23
    @9
    vv
    @12
    @22
    cpw
    #
    cin
    #
    wrex
    #
    vy
    @22
    wral
    @25
    @28
    vy
    @22
    @4
    @24
    @10
    @22
    wcel
    #
    @28
    @4
    @24
    @29
    wa
    #
    wa
    #
    @10
    vw
    cv
    #
    wcel
    #
    @32
    vs
    cv
    #
    wss
    #
    cJ
    @34
    crest
    co
    #
    ccmp
    wcel
    #
    w3a
    #
    vw
    cJ
    wrex
    vs
    @21
    cpw
    #
    wrex
    #
    @28
    @31
    @1
    @24
    @10
    @21
    wcel
    @40
    @1
    @3
    @30
    simpll
    @4
    @24
    @29
    simprl
    @31
    @22
    @21
    @10
    @21
    cA
    inss1
    @4
    @24
    @29
    simprr
    sseldi
    vw
    ccmp
    @10
    @21
    cJ
    vs
    nlly2i
    syl3anc
    @31
    @38
    @28
    vs
    vw
    @39
    cJ
    @31
    @34
    @39
    wcel
    #
    @32
    cJ
    wcel
    #
    wa
    #
    @38
    @28
    @31
    @43
    @38
    wa
    #
    wa
    #
    @34
    cA
    cin
    #
    @27
    wcel
    @5
    @46
    crest
    co
    #
    ccmp
    wcel
    #
    @28
    @45
    @12
    @26
    @46
    @45
    @6
    @32
    cA
    cin
    #
    @12
    wcel
    #
    @49
    @46
    wss
    #
    @46
    @5
    cuni
    #
    wss
    @46
    @12
    wcel
    @4
    @6
    @30
    @44
    @20
    ad2antrr
    #
    @45
    @6
    @49
    @5
    wcel
    #
    @10
    @49
    wcel
    @50
    @53
    @45
    @18
    @3
    @42
    @54
    @1
    @18
    @3
    @30
    @44
    @19
    ad3antrrr
    #
    @1
    @3
    @30
    @44
    simpllr
    #
    @31
    @41
    @42
    @38
    simprlr
    @32
    cA
    cJ
    ctop
    @2
    elrestr
    syl3anc
    @45
    @32
    cA
    @10
    @33
    @35
    @37
    @43
    @31
    simprr1
    @45
    @22
    cA
    @10
    @21
    cA
    inss2
    @4
    @24
    @29
    @44
    simplrr
    sseldi
    elind
    @10
    @5
    @49
    opnneip
    syl3anc
    @45
    @35
    @51
    @33
    @35
    @37
    @43
    @31
    simprr2
    @32
    @34
    cA
    ssrin
    syl
    @45
    cA
    @46
    @52
    @34
    cA
    inss2
    #
    @45
    @18
    cA
    cJ
    cuni
    #
    wss
    #
    cA
    @52
    wceq
    @55
    @45
    @3
    @59
    @56
    cA
    cJ
    @58
    @58
    eqid
    #
    cldss
    syl
    cA
    cJ
    @58
    @60
    restuni
    syl2anc
    syl5sseq
    @11
    @5
    @46
    @49
    @52
    @52
    eqid
    ssnei2
    syl22anc
    @45
    @46
    @22
    wss
    #
    @46
    @26
    wcel
    @45
    @34
    @21
    wss
    @61
    @45
    @34
    @21
    @31
    @41
    @42
    @38
    simprll
    #
    elpwid
    #
    @34
    @21
    cA
    ssrin
    syl
    @46
    @22
    @34
    cA
    vs
    vex
    inex1
    elpw
    sylibr
    elind
    @45
    @47
    @36
    @46
    crest
    co
    #
    ccmp
    @45
    @47
    cJ
    @46
    crest
    co
    #
    @64
    @45
    @18
    @46
    cA
    wss
    #
    @3
    @47
    @65
    wceq
    @55
    @66
    @45
    @57
    a1i
    @56
    @46
    cA
    cJ
    ctop
    @2
    restabs
    syl3anc
    @45
    @18
    @46
    @34
    wss
    #
    @41
    @64
    @65
    wceq
    @55
    @67
    @45
    @34
    cA
    inss1
    a1i
    @62
    @46
    @34
    cJ
    ctop
    @39
    restabs
    syl3anc
    eqtr4d
    @45
    @37
    @46
    @36
    ccld
    cfv
    #
    wcel
    @64
    ccmp
    wcel
    @33
    @35
    @37
    @43
    @31
    simprr3
    @45
    @46
    cA
    @34
    cin
    #
    @68
    @34
    cA
    incom
    @45
    @69
    @68
    wcel
    #
    @69
    @7
    @34
    cin
    #
    wceq
    #
    vv
    @2
    wrex
    #
    @45
    @3
    @69
    @69
    wceq
    #
    @73
    @56
    @69
    eqid
    @72
    @74
    vv
    cA
    @2
    @7
    cA
    wceq
    @71
    @69
    @69
    @7
    cA
    @34
    ineq1
    eqeq2d
    rspcev
    sylancl
    @45
    @18
    @34
    @58
    wss
    @70
    @73
    wb
    @55
    @45
    @34
    @21
    @58
    @63
    @45
    @24
    @21
    @58
    wss
    @4
    @24
    @29
    @44
    simplrl
    @21
    cJ
    elssuni
    syl
    sstrd
    vv
    @69
    @34
    cJ
    @58
    @60
    restcld
    syl2anc
    mpbird
    syl5eqel
    @46
    @36
    cmpcld
    syl2anc
    eqeltrd
    @9
    @48
    vv
    @46
    @27
    @7
    @46
    wceq
    @8
    @47
    ccmp
    @7
    @46
    @5
    crest
    oveq2
    eleq1d
    rspcev
    syl2anc
    expr
    rexlimdvva
    mpd
    anassrs
    ralrimiva
    @16
    @28
    vy
    @13
    @22
    @23
    @9
    vv
    @15
    @27
    @23
    @14
    @26
    @12
    @13
    @22
    pweq
    ineq2d
    rexeqdv
    raleqbi1dv
    syl5ibrcom
    rexlimdva
    sylbid
    ralrimiv
    vx
    vy
    vv
    ccmp
    @5
    isnlly
    sylanbrc
end
