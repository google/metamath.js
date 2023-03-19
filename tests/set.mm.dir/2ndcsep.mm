include "c2ndc.mm"
include "wcel.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "ctb.mm"
include "wrex.mm"
include "ccl.mm"
include "cpw.mm"
include "is2ndc.mm"
include "cuni.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "wral.mm"
include "wel.mm"
include "wex.mm"
include "cvv.mm"
include "wss.mm"
include "vex.mm"
include "difss.mm"
include "ssdomg.mm"
include "mp2.mm"
include "simpr.mm"
include "domtr.mm"
include "sylancr.mm"
include "wne.mm"
include "eldifsn.mm"
include "n0.mm"
include "elunii.mm"
include "simpl.mm"
include "jca.mm"
include "expcom.mm"
include "eximdv.mm"
include "imp.mm"
include "df-rex.mm"
include "sylibr.mm"
include "sylan2b.mm"
include "sylbi.mm"
include "rgen.mm"
include "vuniex.mm"
include "eleq1.mm"
include "axcc4dom.mm"
include "sylancl.mm"
include "crn.mm"
include "frn.mm"
include "ad2antrl.mm"
include "rnex.mm"
include "elpw.mm"
include "ccrd.mm"
include "cdm.mm"
include "wfo.mm"
include "con0.mm"
include "omelon.mm"
include "adantr.mm"
include "ondomen.mm"
include "ssnum.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "sylib.mm"
include "fodomnum.mm"
include "sylc.mm"
include "syl2anc.mm"
include "ctop.mm"
include "tgcl.mm"
include "ad2antrr.mm"
include "unitg.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "clsss3.mm"
include "cin.mm"
include "wi.mm"
include "ne0i.mm"
include "anim2i.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "inelcm.mm"
include "syl.mm"
include "ex.mm"
include "a2d.mm"
include "syl7.mm"
include "exp4a.mm"
include "ralimdv2.mm"
include "ad2antlr.mm"
include "eqidd.mm"
include "a1i.mm"
include "simplll.mm"
include "elcls3.mm"
include "mpbird.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "breq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "exlimddv.mm"
include "unieq.mm"
include "3eqtr4g.mm"
include "pweqd.mm"
include "fveq1d.mm"
include "eqeq12d.mm"
include "anbi2d.mm"
include "rexeqbidv.mm"
include "syl5ibcom.mm"
include "impr.mm"
include "rexlimiva.mm"

theorem 2ndcsep
  let vx: setvar x
  let cJ: class J
  let cX: class X
  let vb: setvar b
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z
  assume 2ndcsep.1: |- X = U. J

  disjoint J x
  disjoint X x
  disjoint b f
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint J b
  disjoint X b
  assert |- ( J e. 2ndc -> E. x e. ~P X ( x ~<_ _om /\ ( ( cls ` J ) ` x ) = X ) )

  proof
    cJ
    c2ndc
    wcel
    vb
    cv
    #
    com
    cdom
    wbr
    #
    @0
    ctg
    cfv
    #
    cJ
    wceq
    #
    wa
    #
    vb
    ctb
    wrex
    vx
    cv
    #
    com
    cdom
    wbr
    #
    @5
    cJ
    ccl
    cfv
    #
    cfv
    #
    cX
    wceq
    #
    wa
    #
    vx
    cX
    cpw
    #
    wrex
    #
    vb
    cJ
    is2ndc
    @4
    @12
    vb
    ctb
    @0
    ctb
    wcel
    #
    @1
    @3
    @12
    @13
    @1
    wa
    #
    @6
    @5
    @2
    ccl
    cfv
    #
    cfv
    #
    @0
    cuni
    #
    wceq
    #
    wa
    #
    vx
    @17
    cpw
    #
    wrex
    #
    @3
    @12
    @14
    @0
    c0
    csn
    #
    cdif
    #
    @17
    vf
    cv
    #
    wf
    #
    vy
    cv
    #
    @24
    cfv
    #
    @26
    wcel
    #
    vy
    @23
    wral
    #
    wa
    #
    @21
    vf
    @14
    @23
    com
    cdom
    wbr
    #
    vz
    vy
    wel
    #
    vz
    @17
    wrex
    #
    vy
    @23
    wral
    @30
    vf
    wex
    @14
    @23
    @0
    cdom
    wbr
    #
    @1
    @31
    @0
    cvv
    wcel
    #
    @23
    @0
    wss
    #
    @34
    vb
    vex
    #
    @0
    @22
    difss
    #
    @23
    @0
    cvv
    ssdomg
    mp2
    @13
    @1
    simpr
    #
    @23
    @0
    com
    domtr
    sylancr
    #
    @33
    vy
    @23
    @26
    @23
    wcel
    #
    vy
    vb
    wel
    #
    @26
    c0
    wne
    #
    wa
    #
    @33
    @26
    @0
    c0
    eldifsn
    #
    @43
    @42
    @32
    vz
    wex
    #
    @33
    vz
    @26
    n0
    @42
    @46
    wa
    vz
    cv
    #
    @17
    wcel
    #
    @32
    wa
    #
    vz
    wex
    #
    @33
    @42
    @46
    @50
    @42
    @32
    @49
    vz
    @32
    @42
    @49
    @32
    @42
    wa
    @48
    @32
    @47
    @26
    @0
    elunii
    @32
    @42
    simpl
    jca
    expcom
    eximdv
    imp
    @32
    vz
    @17
    df-rex
    sylibr
    sylan2b
    sylbi
    rgen
    @32
    @28
    vz
    @17
    vf
    vy
    @23
    vb
    vuniex
    @47
    @27
    @26
    eleq1
    axcc4dom
    sylancl
    @14
    @30
    wa
    #
    @24
    crn
    #
    @20
    wcel
    #
    @52
    com
    cdom
    wbr
    #
    @52
    @15
    cfv
    #
    @17
    wceq
    #
    @21
    @51
    @52
    @17
    wss
    #
    @53
    @25
    @57
    @14
    @29
    @23
    @17
    @24
    frn
    ad2antrl
    #
    @52
    @17
    @24
    vf
    vex
    rnex
    elpw
    sylibr
    @51
    @52
    @23
    cdom
    wbr
    #
    @31
    @54
    @51
    @23
    ccrd
    cdm
    #
    wcel
    #
    @23
    @52
    @24
    wfo
    #
    @59
    @51
    @0
    @60
    wcel
    #
    @36
    @61
    @51
    com
    con0
    wcel
    @1
    @63
    omelon
    @14
    @1
    @30
    @39
    adantr
    com
    @0
    ondomen
    sylancr
    @38
    @0
    @23
    ssnum
    sylancl
    @51
    @24
    @23
    wfn
    #
    @62
    @25
    @64
    @14
    @29
    @23
    @17
    @24
    ffn
    #
    ad2antrl
    @23
    @24
    dffn4
    sylib
    @23
    @52
    @24
    fodomnum
    sylc
    @14
    @31
    @30
    @40
    adantr
    @52
    @23
    com
    domtr
    syl2anc
    @51
    @55
    @17
    @51
    @2
    ctop
    wcel
    #
    @57
    @55
    @17
    wss
    @13
    @66
    @1
    @30
    @0
    tgcl
    ad2antrr
    @58
    @52
    @2
    @17
    @2
    cuni
    #
    @17
    @35
    @67
    @17
    wceq
    @37
    @0
    cvv
    unitg
    ax-mp
    eqcomi
    #
    clsss3
    syl2anc
    @51
    vx
    @17
    @55
    @51
    @5
    @17
    wcel
    #
    @5
    @55
    wcel
    #
    @51
    @69
    wa
    #
    @70
    vx
    vy
    wel
    #
    @26
    @52
    cin
    c0
    wne
    #
    wi
    #
    vy
    @0
    wral
    #
    @30
    @75
    @14
    @69
    @25
    @29
    @75
    @25
    @28
    @74
    vy
    @23
    @0
    @25
    @41
    @28
    wi
    #
    @42
    @72
    @73
    @42
    @72
    wa
    #
    @41
    @25
    @76
    @73
    @77
    @44
    @41
    @72
    @43
    @42
    @26
    @5
    ne0i
    anim2i
    @45
    sylibr
    @25
    @41
    @28
    @73
    @25
    @41
    @28
    @73
    wi
    #
    @25
    @41
    wa
    @27
    @52
    wcel
    #
    @78
    @25
    @64
    @41
    @79
    @65
    @23
    @26
    @24
    fnfvelrn
    sylan
    @28
    @79
    @73
    @27
    @26
    @52
    inelcm
    expcom
    syl
    ex
    a2d
    syl7
    exp4a
    ralimdv2
    imp
    ad2antlr
    @71
    vy
    @0
    @5
    @52
    @2
    @17
    @71
    @2
    eqidd
    @17
    @67
    wceq
    @71
    @68
    a1i
    @13
    @1
    @30
    @69
    simplll
    @51
    @57
    @69
    @58
    adantr
    @51
    @69
    simpr
    elcls3
    mpbird
    ex
    ssrdv
    eqssd
    @19
    @54
    @56
    wa
    vx
    @52
    @20
    @5
    @52
    wceq
    #
    @6
    @54
    @18
    @56
    @5
    @52
    com
    cdom
    breq1
    @80
    @16
    @55
    @17
    @5
    @52
    @15
    fveq2
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    exlimddv
    @3
    @19
    @10
    vx
    @20
    @11
    @3
    @17
    cX
    @3
    @67
    cJ
    cuni
    @17
    cX
    @2
    cJ
    unieq
    @68
    2ndcsep.1
    3eqtr4g
    #
    pweqd
    @3
    @18
    @9
    @6
    @3
    @16
    @8
    @17
    cX
    @3
    @5
    @15
    @7
    @2
    cJ
    ccl
    fveq2
    fveq1d
    @81
    eqeq12d
    anbi2d
    rexeqbidv
    syl5ibcom
    impr
    rexlimiva
    sylbi
end
