include "cmin.mm"
include "co.mm"
include "cicc.mm"
include "cv.mm"
include "caddc.mm"
include "cfv.mm"
include "citg.mm"
include "cdit.mm"
include "cioo.mm"
include "ltled.mm"
include "lesub1dd.mm"
include "ditgpos.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cif.mm"
include "crn.mm"
include "cmpt.mm"
include "cres.mm"
include "iftrue.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "adantlr.mm"
include "wn.mm"
include "iffalse.mm"
include "sylan9eq.mm"
include "adantll.mm"
include "ad2antlr.mm"
include "cxr.mm"
include "rexrd.mm"
include "ad3antrrr.mm"
include "cr.mm"
include "adantr.mm"
include "simpr.mm"
include "eliccre.mm"
include "syl3anc.mm"
include "ad2antrr.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp2d.mm"
include "wne.mm"
include "neqne.mm"
include "leneltd.mm"
include "simp3d.mm"
include "nesym.mm"
include "biimpri.mm"
include "eliood.mm"
include "fvres.mm"
include "syl.mm"
include "3eqtr4d.mm"
include "pm2.61dan.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "eqeq1.mm"
include "fveq2.mm"
include "ifbieq2d.mm"
include "resubcld.mm"
include "elioo2.mm"
include "simp1d.mm"
include "ltsubadd2d.mm"
include "gtned.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "readdcld.mm"
include "ltaddsub2d.mm"
include "mpbird.mm"
include "ltned.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "eliccd.mm"
include "wfun.mm"
include "cdm.mm"
include "cc.mm"
include "wf.mm"
include "ffun.mm"
include "fdm.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "fvelrn.mm"
include "fvmptd.mm"
include "itgeq2dv.mm"
include "wss.mm"
include "frn.mm"
include "lesubadd2d.mm"
include "leaddsub2d.mm"
include "sseldd.mm"
include "itgioo.mm"
include "3eqtrrd.mm"
include "nfv.mm"
include "climc.mm"
include "limcicciooub.mm"
include "eleqtrrd.mm"
include "limciccioolb.mm"
include "cncfiooicc.mm"
include "itgsbtaddcnst.mm"
include "cbvitgv.mm"
include "a1i.mm"
include "simplr.mm"
include "breqtrrd.mm"
include "eqeltrd.mm"
include "eqbrtrd.mm"
include "3eqtrd.mm"
include "ioossicc.mm"
include "sseldi.mm"
include "ffvelrnda.mm"

theorem fourierdlem82
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cG: class G
  let cL: class L
  let cX: class X
  let vs: setvar s
  let vk: setvar k
  assume fourierdlem82.1: |- G = ( x e. ( A [,] B ) |-> if ( x = A , R , if ( x = B , L , ( ( F |` ( A (,) B ) ) ` x ) ) ) )
  assume fourierdlem82.2: |- ( ph -> A e. RR )
  assume fourierdlem82.3: |- ( ph -> B e. RR )
  assume fourierdlem82.4: |- ( ph -> A < B )
  assume fourierdlem82.5: |- ( ph -> F : ( A [,] B ) --> CC )
  assume fourierdlem82.6: |- ( ph -> ( F |` ( A (,) B ) ) e. ( ( A (,) B ) -cn-> CC ) )
  assume fourierdlem82.7: |- ( ph -> L e. ( F limCC B ) )
  assume fourierdlem82.8: |- ( ph -> R e. ( F limCC A ) )
  assume fourierdlem82.9: |- ( ph -> X e. RR )

  disjoint A t
  disjoint A x
  disjoint t x
  disjoint B t
  disjoint B x
  disjoint F x
  disjoint G t
  disjoint L x
  disjoint R x
  disjoint X t
  disjoint X x
  disjoint ph t
  disjoint ph x
  disjoint A s
  disjoint s t
  disjoint B s
  disjoint G s
  disjoint X s
  disjoint ph s
  disjoint k x
  assert |- ( ph -> S. ( A [,] B ) ( F ` t ) _d t = S. ( ( A - X ) [,] ( B - X ) ) ( F ` ( X + t ) ) _d t )

  proof
    wph
    vt
    cA
    cX
    cmin
    co
    #
    cB
    cX
    cmin
    co
    #
    cicc
    co
    #
    cX
    vt
    cv
    #
    caddc
    co
    #
    cF
    cfv
    #
    citg
    #
    vt
    @0
    @1
    @4
    cG
    cfv
    #
    cdit
    #
    vs
    cA
    cB
    vs
    cv
    #
    cG
    cfv
    #
    cdit
    #
    vt
    cA
    cB
    cicc
    co
    #
    @3
    cF
    cfv
    #
    citg
    #
    wph
    @8
    vt
    @0
    @1
    cioo
    co
    #
    @7
    citg
    vt
    @15
    @5
    citg
    @6
    wph
    vt
    @0
    @1
    @7
    wph
    cA
    cB
    cX
    fourierdlem82.2
    fourierdlem82.3
    fourierdlem82.9
    wph
    cA
    cB
    fourierdlem82.2
    fourierdlem82.3
    fourierdlem82.4
    ltled
    #
    lesub1dd
    ditgpos
    wph
    vt
    @15
    @7
    @5
    wph
    @3
    @15
    wcel
    #
    wa
    #
    vx
    @4
    vx
    cv
    #
    cA
    wceq
    #
    cR
    @19
    cB
    wceq
    #
    cL
    @19
    cF
    cfv
    #
    cif
    #
    cif
    #
    @5
    @12
    cG
    cF
    crn
    #
    wph
    cG
    vx
    @12
    @24
    cmpt
    #
    wceq
    @17
    wph
    cG
    vx
    @12
    @20
    cR
    @21
    cL
    @19
    cF
    cA
    cB
    cioo
    co
    #
    cres
    #
    cfv
    #
    cif
    #
    cif
    #
    cmpt
    #
    @26
    fourierdlem82.1
    wph
    vx
    @12
    @31
    @24
    wph
    @19
    @12
    wcel
    #
    wa
    #
    @20
    @31
    @24
    wceq
    #
    wph
    @20
    @35
    @33
    wph
    @20
    wa
    @31
    cR
    @24
    @20
    @31
    cR
    wceq
    wph
    @20
    cR
    @30
    iftrue
    adantl
    @20
    @24
    cR
    wceq
    wph
    @20
    cR
    @23
    iftrue
    adantl
    eqtr4d
    adantlr
    @34
    @20
    wn
    #
    wa
    #
    @21
    @35
    @37
    @21
    wa
    @31
    cL
    @24
    @36
    @21
    @31
    cL
    wceq
    @34
    @36
    @21
    @31
    @30
    cL
    @20
    cR
    @30
    iffalse
    #
    @21
    cL
    @29
    iftrue
    sylan9eq
    adantll
    @36
    @21
    @24
    cL
    wceq
    @34
    @36
    @21
    @24
    @23
    cL
    @20
    cR
    @23
    iffalse
    #
    @21
    cL
    @22
    iftrue
    sylan9eq
    adantll
    eqtr4d
    @37
    @21
    wn
    #
    wa
    #
    @30
    @29
    @31
    @24
    @40
    @30
    @29
    wceq
    @37
    @21
    cL
    @29
    iffalse
    adantl
    @36
    @31
    @30
    wceq
    @34
    @40
    @38
    ad2antlr
    @41
    @23
    @22
    @24
    @29
    @40
    @23
    @22
    wceq
    @37
    @21
    cL
    @22
    iffalse
    adantl
    @36
    @24
    @23
    wceq
    @34
    @40
    @39
    ad2antlr
    @41
    @19
    @27
    wcel
    #
    @29
    @22
    wceq
    #
    @41
    cA
    cB
    @19
    wph
    cA
    cxr
    wcel
    #
    @33
    @36
    @40
    wph
    cA
    fourierdlem82.2
    rexrd
    #
    ad3antrrr
    wph
    cB
    cxr
    wcel
    #
    @33
    @36
    @40
    wph
    cB
    fourierdlem82.3
    rexrd
    #
    ad3antrrr
    @34
    @19
    cr
    wcel
    #
    @36
    @40
    @34
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @33
    @48
    wph
    @49
    @33
    fourierdlem82.2
    adantr
    #
    wph
    @50
    @33
    fourierdlem82.3
    adantr
    #
    wph
    @33
    simpr
    #
    cA
    cB
    @19
    eliccre
    syl3anc
    #
    ad2antrr
    @37
    cA
    @19
    clt
    wbr
    @40
    @37
    cA
    @19
    wph
    @49
    @33
    @36
    fourierdlem82.2
    ad2antrr
    @34
    @48
    @36
    @54
    adantr
    @34
    cA
    @19
    cle
    wbr
    #
    @36
    @34
    @48
    @55
    @19
    cB
    cle
    wbr
    #
    @34
    @33
    @48
    @55
    @56
    w3a
    #
    @53
    @34
    @49
    @50
    @33
    @57
    wb
    @51
    @52
    cA
    cB
    @19
    elicc2
    syl2anc
    mpbid
    #
    simp2d
    adantr
    @36
    @19
    cA
    wne
    @34
    @19
    cA
    neqne
    adantl
    leneltd
    adantr
    @34
    @40
    @19
    cB
    clt
    wbr
    @36
    @34
    @40
    wa
    @19
    cB
    @34
    @48
    @40
    @54
    adantr
    wph
    @50
    @33
    @40
    fourierdlem82.3
    ad2antrr
    @34
    @56
    @40
    @34
    @48
    @55
    @56
    @58
    simp3d
    adantr
    @40
    cB
    @19
    wne
    #
    @34
    @59
    @40
    cB
    @19
    nesym
    biimpri
    adantl
    leneltd
    adantlr
    eliood
    @19
    @27
    cF
    fvres
    #
    syl
    3eqtr4d
    3eqtr4d
    pm2.61dan
    pm2.61dan
    mpteq2dva
    syl5eq
    adantr
    @19
    @4
    wceq
    #
    @18
    @24
    @4
    cA
    wceq
    #
    cR
    @4
    cB
    wceq
    #
    cL
    @5
    cif
    #
    cif
    #
    @5
    @61
    @20
    @62
    @23
    @64
    cR
    @19
    @4
    cA
    eqeq1
    @61
    @21
    @63
    @22
    @5
    cL
    @19
    @4
    cB
    eqeq1
    @19
    @4
    cF
    fveq2
    ifbieq2d
    ifbieq2d
    @18
    @65
    @64
    @5
    @18
    @62
    cR
    @64
    @18
    @4
    cA
    @18
    cA
    @4
    wph
    @49
    @17
    fourierdlem82.2
    adantr
    #
    @18
    @0
    @3
    clt
    wbr
    #
    cA
    @4
    clt
    wbr
    @18
    @3
    cr
    wcel
    #
    @67
    @3
    @1
    clt
    wbr
    #
    @18
    @17
    @68
    @67
    @69
    w3a
    #
    wph
    @17
    simpr
    @18
    @0
    cxr
    wcel
    #
    @1
    cxr
    wcel
    #
    @17
    @70
    wb
    wph
    @71
    @17
    wph
    @0
    wph
    cA
    cX
    fourierdlem82.2
    fourierdlem82.9
    resubcld
    #
    rexrd
    adantr
    wph
    @72
    @17
    wph
    @1
    wph
    cB
    cX
    fourierdlem82.3
    fourierdlem82.9
    resubcld
    #
    rexrd
    adantr
    @0
    @1
    @3
    elioo2
    syl2anc
    mpbid
    #
    simp2d
    @18
    cA
    cX
    @3
    @66
    wph
    cX
    cr
    wcel
    #
    @17
    fourierdlem82.9
    adantr
    #
    @18
    @68
    @67
    @69
    @75
    simp1d
    #
    ltsubadd2d
    mpbid
    #
    gtned
    neneqd
    iffalsed
    @18
    @63
    cL
    @5
    @18
    @4
    cB
    @18
    @4
    cB
    @18
    cX
    @3
    @77
    @78
    readdcld
    #
    @18
    @4
    cB
    clt
    wbr
    @69
    @18
    @68
    @67
    @69
    @75
    simp3d
    @18
    cX
    @3
    cB
    @77
    @78
    wph
    @50
    @17
    fourierdlem82.3
    adantr
    #
    ltaddsub2d
    mpbird
    #
    ltned
    neneqd
    iffalsed
    eqtrd
    sylan9eqr
    @18
    cA
    cB
    @4
    @66
    @81
    @80
    @18
    cA
    @4
    @66
    @80
    @79
    ltled
    @18
    @4
    cB
    @80
    @81
    @82
    ltled
    eliccd
    #
    @18
    cF
    wfun
    #
    @4
    cF
    cdm
    #
    wcel
    #
    @5
    @25
    wcel
    #
    wph
    @84
    @17
    wph
    @12
    cc
    cF
    wf
    #
    @84
    fourierdlem82.5
    @12
    cc
    cF
    ffun
    syl
    #
    adantr
    @18
    @4
    @12
    @85
    @83
    wph
    @12
    @85
    wceq
    #
    @17
    wph
    @85
    @12
    wph
    @88
    @85
    @12
    wceq
    fourierdlem82.5
    @12
    cc
    cF
    fdm
    syl
    eqcomd
    #
    adantr
    eleqtrd
    @4
    cF
    fvelrn
    #
    syl2anc
    fvmptd
    itgeq2dv
    wph
    vt
    @0
    @1
    @5
    @73
    @74
    wph
    @3
    @2
    wcel
    #
    wa
    #
    @25
    cc
    @5
    wph
    @25
    cc
    wss
    #
    @93
    wph
    @88
    @95
    fourierdlem82.5
    @12
    cc
    cF
    frn
    syl
    adantr
    @94
    @84
    @86
    @87
    wph
    @84
    @93
    @89
    adantr
    @94
    @4
    @12
    @85
    @94
    cA
    cB
    @4
    wph
    @49
    @93
    fourierdlem82.2
    adantr
    #
    wph
    @50
    @93
    fourierdlem82.3
    adantr
    #
    @94
    cX
    @3
    wph
    @76
    @93
    fourierdlem82.9
    adantr
    #
    @94
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @93
    @68
    wph
    @99
    @93
    @73
    adantr
    #
    wph
    @100
    @93
    @74
    adantr
    #
    wph
    @93
    simpr
    #
    @0
    @1
    @3
    eliccre
    syl3anc
    #
    readdcld
    @94
    @0
    @3
    cle
    wbr
    #
    cA
    @4
    cle
    wbr
    @94
    @68
    @105
    @3
    @1
    cle
    wbr
    #
    @94
    @93
    @68
    @105
    @106
    w3a
    #
    @103
    @94
    @99
    @100
    @93
    @107
    wb
    @101
    @102
    @0
    @1
    @3
    elicc2
    syl2anc
    mpbid
    #
    simp2d
    @94
    cA
    cX
    @3
    @96
    @98
    @104
    lesubadd2d
    mpbid
    @94
    @4
    cB
    cle
    wbr
    @106
    @94
    @68
    @105
    @106
    @108
    simp3d
    @94
    cX
    @3
    cB
    @98
    @104
    @97
    leaddsub2d
    mpbird
    eliccd
    wph
    @90
    @93
    @91
    adantr
    eleqtrd
    @92
    syl2anc
    sseldd
    itgioo
    3eqtrrd
    wph
    vs
    cA
    cB
    cG
    cX
    vt
    fourierdlem82.2
    fourierdlem82.3
    @16
    fourierdlem82.9
    wph
    vx
    cA
    cB
    cR
    @28
    cG
    cL
    wph
    vx
    nfv
    fourierdlem82.1
    fourierdlem82.2
    fourierdlem82.3
    fourierdlem82.6
    wph
    cL
    cF
    cB
    climc
    co
    @28
    cB
    climc
    co
    fourierdlem82.7
    wph
    cA
    cB
    cF
    fourierdlem82.2
    fourierdlem82.3
    fourierdlem82.4
    fourierdlem82.5
    limcicciooub
    eleqtrrd
    wph
    cR
    cF
    cA
    climc
    co
    @28
    cA
    climc
    co
    fourierdlem82.8
    wph
    cA
    cB
    cF
    fourierdlem82.2
    fourierdlem82.3
    fourierdlem82.4
    fourierdlem82.5
    limciccioolb
    eleqtrrd
    cncfiooicc
    itgsbtaddcnst
    wph
    @11
    vs
    @27
    @10
    citg
    #
    vt
    @27
    @13
    citg
    #
    @14
    wph
    vs
    cA
    cB
    @10
    @16
    ditgpos
    wph
    @109
    vt
    @27
    @3
    cG
    cfv
    #
    citg
    @110
    vs
    vt
    @27
    @10
    @111
    @9
    @3
    cG
    fveq2
    cbvitgv
    wph
    vt
    @27
    @111
    @13
    wph
    @3
    @27
    wcel
    #
    wa
    #
    vx
    @3
    @31
    @13
    @12
    cG
    @25
    cG
    @32
    wceq
    @113
    fourierdlem82.1
    a1i
    @113
    @19
    @3
    wceq
    #
    wa
    #
    @31
    @30
    @29
    @13
    @115
    @20
    cR
    @30
    @115
    @19
    cA
    @115
    cA
    @19
    wph
    @49
    @112
    @114
    fourierdlem82.2
    ad2antrr
    @115
    cA
    @3
    @19
    clt
    @115
    @68
    cA
    @3
    clt
    wbr
    #
    @3
    cB
    clt
    wbr
    #
    @115
    @112
    @68
    @116
    @117
    w3a
    #
    wph
    @112
    @114
    simplr
    #
    @115
    @44
    @46
    @112
    @118
    wb
    wph
    @44
    @112
    @114
    @45
    ad2antrr
    wph
    @46
    @112
    @114
    @47
    ad2antrr
    cA
    cB
    @3
    elioo2
    syl2anc
    mpbid
    #
    simp2d
    @113
    @114
    simpr
    #
    breqtrrd
    gtned
    neneqd
    iffalsed
    @115
    @21
    cL
    @29
    @115
    @19
    cB
    @115
    @19
    cB
    @115
    @19
    @3
    cr
    @121
    @115
    @68
    @116
    @117
    @120
    simp1d
    eqeltrd
    @115
    @19
    @3
    cB
    clt
    @121
    @115
    @68
    @116
    @117
    @120
    simp3d
    eqbrtrd
    ltned
    neneqd
    iffalsed
    @115
    @29
    @22
    @13
    @115
    @42
    @43
    @115
    @19
    @3
    @27
    @121
    @119
    eqeltrd
    @60
    syl
    @114
    @22
    @13
    wceq
    @113
    @19
    @3
    cF
    fveq2
    adantl
    eqtrd
    3eqtrd
    @113
    @27
    @12
    @3
    cA
    cB
    ioossicc
    wph
    @112
    simpr
    sseldi
    #
    @113
    @84
    @3
    @85
    wcel
    @13
    @25
    wcel
    wph
    @84
    @112
    @89
    adantr
    @113
    @3
    @12
    @85
    @122
    wph
    @90
    @112
    @91
    adantr
    eleqtrd
    @3
    cF
    fvelrn
    syl2anc
    fvmptd
    itgeq2dv
    syl5eq
    wph
    vt
    cA
    cB
    @13
    fourierdlem82.2
    fourierdlem82.3
    wph
    @12
    cc
    @3
    cF
    fourierdlem82.5
    ffvelrnda
    itgioo
    3eqtrd
    3eqtrrd
end
