include "cc.mm"
include "wss.mm"
include "ccmp.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "cv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wa.mm"
include "cha.mm"
include "crest.mm"
include "co.mm"
include "cnfldhaus.mm"
include "a1i.mm"
include "simpl.mm"
include "simpr.mm"
include "syl5eqelr.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "hauscmp.mm"
include "syl3anc.mm"
include "cuni.mm"
include "wceq.mm"
include "crp.mm"
include "wf.mm"
include "cc0.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "cin.mm"
include "wex.mm"
include "cpw.mm"
include "cfn.mm"
include "wel.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "restuni.mm"
include "sylancr.mm"
include "unieqi.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "c1.mm"
include "caddc.mm"
include "cvv.mm"
include "cnex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "adantr.mm"
include "cxmt.mm"
include "cxr.mm"
include "cnxmet.mm"
include "0cnd.mm"
include "sselda.mm"
include "abscld.mm"
include "peano2re.mm"
include "syl.mm"
include "rexrd.mm"
include "cnfldtopn.mm"
include "blopn.mm"
include "elrestr.mm"
include "syl6eleqr.mm"
include "clt.mm"
include "0cn.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "mpan.mm"
include "cneg.mm"
include "df-neg.mm"
include "fveq2i.mm"
include "absneg.mm"
include "syl5eqr.mm"
include "eqtrd.mm"
include "ltp1d.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "elbl.mm"
include "mpbir2and.mm"
include "elind.mm"
include "absge0d.mm"
include "ge0p1rpd.mm"
include "oveq2.mm"
include "ineq1d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "eleq2.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "syl12anc.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "cmpcovf.mm"
include "syl2anc.mm"
include "ad4antr.mm"
include "simpllr.mm"
include "eluni2.mm"
include "syl6bb.mm"
include "elssuni.mm"
include "ad2antrl.mm"
include "sseqtr4d.mm"
include "simp-6l.mm"
include "sstrd.mm"
include "simprr.mm"
include "sseldd.mm"
include "simplrl.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "ffvelrnd.mm"
include "rpred.mm"
include "inss1.mm"
include "id.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eleqtrd.mm"
include "sseldi.mm"
include "rpxrd.mm"
include "mpbid.mm"
include "simprd.mm"
include "eqbrtrrd.mm"
include "simplrr.mm"
include "breq1d.mm"
include "ltletrd.mm"
include "ltled.mm"
include "rexlimdvaa.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "inss2.mm"
include "ffvelrn.mm"
include "fimaxre3.mm"
include "reximddv.mm"
include "ex.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "jca.mm"
include "ci.mm"
include "cmul.mm"
include "cmpt2.mm"
include "cicc.mm"
include "cxp.mm"
include "cima.mm"
include "cnheiborlem.mm"
include "imp.mm"
include "adantl.mm"
include "impbida.mm"

theorem cnheibor
  let vx: setvar x
  let cT: class T
  let cJ: class J
  let cX: class X
  let vr: setvar r
  let vu: setvar u
  let vz: setvar z
  let cF: class F
  let cR: class R
  let vf: setvar f
  let vs: setvar s
  let vy: setvar y
  assume cnheibor.2: |- J = ( TopOpen ` CCfld )
  assume cnheibor.3: |- T = ( J |`t X )

  disjoint r x
  disjoint T r
  disjoint T x
  disjoint J r
  disjoint J x
  disjoint X r
  disjoint X x
  disjoint u z
  disjoint F u
  disjoint F z
  disjoint R u
  disjoint R z
  disjoint f r
  disjoint f s
  disjoint f u
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint T f
  disjoint r s
  disjoint r u
  disjoint r y
  disjoint r z
  disjoint s u
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint T s
  disjoint u x
  disjoint u y
  disjoint T u
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint T y
  disjoint T z
  disjoint J u
  disjoint J y
  disjoint J z
  disjoint X f
  disjoint X s
  disjoint X u
  disjoint X y
  disjoint X z
  assert |- ( X C_ CC -> ( T e. Comp <-> ( X e. ( Clsd ` J ) /\ E. r e. RR A. x e. X ( abs ` x ) <_ r ) ) )

  proof
    cX
    cc
    wss
    #
    cT
    ccmp
    wcel
    #
    cX
    cJ
    ccld
    cfv
    wcel
    #
    vx
    cv
    #
    cabs
    cfv
    #
    vr
    cv
    #
    cle
    wbr
    #
    vx
    cX
    wral
    #
    vr
    cr
    wrex
    #
    wa
    #
    @0
    @1
    wa
    #
    @2
    @8
    @10
    cJ
    cha
    wcel
    #
    @0
    cJ
    cX
    crest
    co
    #
    ccmp
    wcel
    @2
    @11
    @10
    cJ
    cnheibor.2
    cnfldhaus
    a1i
    @0
    @1
    simpl
    #
    @10
    @12
    cT
    ccmp
    cnheibor.3
    @0
    @1
    simpr
    #
    syl5eqelr
    cX
    cJ
    cc
    cc
    cJ
    cJ
    cnheibor.2
    cnfldtopon
    toponunii
    #
    hauscmp
    syl3anc
    @10
    cT
    cuni
    #
    vs
    cv
    #
    cuni
    #
    wceq
    #
    @17
    crp
    vf
    cv
    #
    wf
    #
    vu
    cv
    #
    cc0
    @22
    @20
    cfv
    #
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    #
    co
    #
    cX
    cin
    #
    wceq
    #
    vu
    @17
    wral
    #
    wa
    #
    vf
    wex
    #
    wa
    #
    vs
    cT
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @8
    @10
    @1
    vx
    vu
    wel
    #
    @22
    cc0
    @5
    @25
    co
    #
    cX
    cin
    #
    wceq
    #
    vr
    crp
    wrex
    #
    wa
    #
    vu
    cT
    wrex
    #
    vx
    @16
    wral
    @35
    @14
    @10
    @42
    vx
    @16
    @10
    @3
    @16
    wcel
    #
    @3
    cX
    wcel
    #
    @42
    @10
    @44
    @43
    @10
    cX
    @16
    @3
    @10
    cX
    @12
    cuni
    #
    @16
    @10
    cJ
    ctop
    wcel
    #
    @0
    cX
    @45
    wceq
    cJ
    cnheibor.2
    cnfldtop
    #
    @13
    cX
    cJ
    cc
    @15
    restuni
    sylancr
    cT
    @12
    cnheibor.3
    unieqi
    syl6eqr
    #
    eleq2d
    biimpar
    @10
    @44
    wa
    #
    cc0
    @4
    c1
    caddc
    co
    #
    @25
    co
    #
    cX
    cin
    #
    cT
    wcel
    @3
    @52
    wcel
    #
    @52
    @38
    wceq
    #
    vr
    crp
    wrex
    #
    @42
    @49
    @52
    @12
    cT
    @49
    @46
    cX
    cvv
    wcel
    #
    @51
    cJ
    wcel
    #
    @52
    @12
    wcel
    @46
    @49
    @47
    a1i
    @10
    @56
    @44
    @10
    @0
    cc
    cvv
    wcel
    @56
    @13
    cnex
    cX
    cc
    cvv
    ssexg
    sylancl
    adantr
    @49
    @24
    cc
    cxmt
    cfv
    wcel
    #
    cc0
    cc
    wcel
    #
    @50
    cxr
    wcel
    #
    @57
    @58
    @49
    cnxmet
    a1i
    #
    @49
    0cnd
    #
    @49
    @50
    @49
    @4
    cr
    wcel
    @50
    cr
    wcel
    @49
    @3
    @10
    cX
    cc
    @3
    @13
    sselda
    #
    abscld
    #
    @4
    peano2re
    syl
    rexrd
    #
    @24
    cc0
    @50
    cJ
    cc
    cJ
    cnheibor.2
    cnfldtopn
    blopn
    syl3anc
    @51
    cX
    cJ
    ctop
    cvv
    elrestr
    syl3anc
    cnheibor.3
    syl6eleqr
    @49
    @51
    cX
    @3
    @49
    @3
    @51
    wcel
    #
    @3
    cc
    wcel
    #
    cc0
    @3
    @24
    co
    #
    @50
    clt
    wbr
    #
    @63
    @49
    @68
    @4
    @50
    clt
    @49
    @67
    @68
    @4
    wceq
    #
    @63
    @67
    @68
    cc0
    @3
    cmin
    co
    #
    cabs
    cfv
    #
    @4
    @59
    @67
    @68
    @72
    wceq
    0cn
    cc0
    @3
    @24
    @24
    eqid
    cnmetdval
    mpan
    @67
    @72
    @3
    cneg
    #
    cabs
    cfv
    @4
    @73
    @71
    cabs
    @3
    df-neg
    fveq2i
    @3
    absneg
    syl5eqr
    eqtrd
    #
    syl
    @49
    @4
    @64
    ltp1d
    eqbrtrd
    @49
    @58
    @59
    @60
    @66
    @67
    @69
    wa
    wb
    @61
    @62
    @65
    @3
    @24
    cc0
    @50
    cc
    elbl
    syl3anc
    mpbir2and
    @10
    @44
    simpr
    elind
    @49
    @50
    crp
    wcel
    @52
    @52
    wceq
    #
    @55
    @49
    @4
    @64
    @49
    @3
    @63
    absge0d
    ge0p1rpd
    @52
    eqid
    @54
    @75
    vr
    @50
    crp
    @5
    @50
    wceq
    #
    @38
    @52
    @52
    @76
    @37
    @51
    cX
    @5
    @50
    cc0
    @25
    oveq2
    ineq1d
    eqeq2d
    rspcev
    sylancl
    @41
    @53
    @55
    wa
    vu
    @52
    cT
    @22
    @52
    wceq
    #
    @36
    @53
    @40
    @55
    @22
    @52
    @3
    eleq2
    @77
    @39
    @54
    vr
    crp
    @22
    @52
    @38
    eqeq1
    rexbidv
    anbi12d
    rspcev
    syl12anc
    syldan
    ralrimiva
    @39
    @28
    vx
    vu
    vr
    crp
    vf
    cT
    @16
    vs
    @16
    eqid
    @5
    @23
    wceq
    #
    @38
    @27
    @22
    @78
    @37
    @26
    cX
    @5
    @23
    cc0
    @25
    oveq2
    ineq1d
    eqeq2d
    cmpcovf
    syl2anc
    @10
    @32
    @8
    vs
    @34
    @10
    @17
    @34
    wcel
    #
    wa
    #
    @19
    @31
    @8
    @80
    @19
    wa
    #
    @30
    @8
    vf
    @81
    @30
    @8
    @81
    @30
    wa
    #
    @23
    @5
    cle
    wbr
    #
    vu
    @17
    wral
    #
    @7
    vr
    cr
    @82
    @5
    cr
    wcel
    #
    @84
    wa
    #
    wa
    #
    @6
    vx
    cX
    @87
    @44
    vx
    vz
    wel
    #
    vz
    @17
    wrex
    #
    @6
    @87
    @44
    @3
    @18
    wcel
    @89
    @87
    cX
    @18
    @3
    @87
    cX
    @16
    @18
    @10
    cX
    @16
    wceq
    @79
    @19
    @30
    @86
    @48
    ad4antr
    @80
    @19
    @30
    @86
    simpllr
    eqtrd
    #
    eleq2d
    vz
    @3
    @17
    eluni2
    syl6bb
    @87
    @88
    @6
    vz
    @17
    @87
    vz
    vs
    wel
    #
    @88
    wa
    #
    wa
    #
    @4
    @5
    @93
    @3
    @93
    vz
    cv
    #
    cc
    @3
    @93
    @94
    cX
    cc
    @93
    @94
    @18
    cX
    @91
    @94
    @18
    wss
    @87
    @88
    @94
    @17
    elssuni
    ad2antrl
    @87
    cX
    @18
    wceq
    @92
    @90
    adantr
    sseqtr4d
    @0
    @1
    @79
    @19
    @30
    @86
    @92
    simp-6l
    sstrd
    @87
    @91
    @88
    simprr
    #
    sseldd
    #
    abscld
    #
    @82
    @85
    @84
    @92
    simplrl
    #
    @93
    @4
    @94
    @20
    cfv
    #
    @5
    @97
    @93
    @99
    @93
    @17
    crp
    @94
    @20
    @82
    @21
    @86
    @92
    @81
    @21
    @29
    simprl
    ad2antrr
    @87
    @91
    @88
    simprl
    #
    ffvelrnd
    #
    rpred
    @98
    @93
    @68
    @4
    @99
    clt
    @93
    @67
    @70
    @96
    @74
    syl
    @93
    @67
    @68
    @99
    clt
    wbr
    #
    @93
    @3
    cc0
    @99
    @25
    co
    #
    wcel
    #
    @67
    @102
    wa
    #
    @93
    @103
    cX
    cin
    #
    @103
    @3
    @103
    cX
    inss1
    @93
    @3
    @94
    @106
    @95
    @93
    @91
    @29
    @94
    @106
    wceq
    #
    @100
    @82
    @29
    @86
    @92
    @81
    @21
    @29
    simprr
    ad2antrr
    @28
    @107
    vu
    @94
    @17
    @22
    @94
    wceq
    #
    @22
    @94
    @27
    @106
    @108
    id
    @108
    @26
    @103
    cX
    @108
    @23
    @99
    cc0
    @25
    @22
    @94
    @20
    fveq2
    #
    oveq2d
    ineq1d
    eqeq12d
    rspcv
    sylc
    eleqtrd
    sseldi
    @93
    @58
    @59
    @99
    cxr
    wcel
    @104
    @105
    wb
    @58
    @93
    cnxmet
    a1i
    @93
    0cnd
    @93
    @99
    @101
    rpxrd
    @3
    @24
    cc0
    @99
    cc
    elbl
    syl3anc
    mpbid
    simprd
    eqbrtrrd
    @93
    @91
    @84
    @99
    @5
    cle
    wbr
    #
    @100
    @82
    @85
    @84
    @92
    simplrr
    @83
    @110
    vu
    @94
    @17
    @108
    @23
    @99
    @5
    cle
    @109
    breq1d
    rspcv
    sylc
    ltletrd
    ltled
    rexlimdvaa
    sylbid
    ralrimiv
    @82
    @17
    cfn
    wcel
    @23
    cr
    wcel
    #
    vu
    @17
    wral
    #
    @84
    vr
    cr
    wrex
    @82
    @34
    cfn
    @17
    @33
    cfn
    inss2
    @10
    @79
    @19
    @30
    simpllr
    sseldi
    @21
    @112
    @81
    @29
    @21
    @111
    vu
    @17
    @21
    vu
    vs
    wel
    wa
    @23
    @17
    crp
    @22
    @20
    ffvelrn
    rpred
    ralrimiva
    ad2antrl
    vr
    vu
    @17
    @23
    fimaxre3
    syl2anc
    reximddv
    ex
    exlimdv
    expimpd
    rexlimdva
    mpd
    jca
    @9
    @1
    @0
    @2
    @8
    @1
    @2
    @7
    @1
    vr
    cr
    vy
    vz
    vx
    @5
    cT
    vy
    vz
    cr
    cr
    vy
    cv
    ci
    @94
    cmul
    co
    caddc
    co
    cmpt2
    #
    cJ
    cX
    @113
    @5
    cneg
    @5
    cicc
    co
    #
    @114
    cxp
    cima
    #
    cnheibor.2
    cnheibor.3
    @113
    eqid
    @115
    eqid
    cnheiborlem
    rexlimdvaa
    imp
    adantl
    impbida
end
