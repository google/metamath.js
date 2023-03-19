include "citg2.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "itg2splitlem.mm"
include "cmin.mm"
include "cv.mm"
include "cofr.mm"
include "citg1.mm"
include "wi.mm"
include "cdm.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "adantr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "wf.mm"
include "cif.mm"
include "adantlr.mm"
include "wn.mm"
include "0e0iccpnf.mm"
include "a1i.mm"
include "ifclda.mm"
include "fmptd.mm"
include "readdcld.mm"
include "itg2lecl.mm"
include "syl3anc.mm"
include "itg1cl.mm"
include "ad2antrl.mm"
include "cof.mm"
include "simprll.mm"
include "simprrl.mm"
include "itg1add.mm"
include "cin.mm"
include "i1fadd.mm"
include "wss.mm"
include "inss1.mm"
include "cvol.mm"
include "mblss.mm"
include "syl.mm"
include "syl5ss.mm"
include "covol.mm"
include "cdif.mm"
include "nfv.mm"
include "nfcv.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfbr.mm"
include "nfan.mm"
include "eldifi.mm"
include "cvv.mm"
include "wfn.mm"
include "i1ff.mm"
include "ffn.mm"
include "reex.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofval.mm"
include "sylan2.mm"
include "cxr.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "rexrd.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "0red.mm"
include "simprrr.mm"
include "wb.mm"
include "fvexd.mm"
include "cun.mm"
include "ssun2.mm"
include "syl5sseqr.mm"
include "sselda.mm"
include "syldan.mm"
include "simpr.mm"
include "dffn5.mm"
include "sylib.mm"
include "ofrfval2.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "eldifn.mm"
include "adantl.mm"
include "elin.mm"
include "sylnib.mm"
include "imnan.mm"
include "sylibr.mm"
include "imp.mm"
include "iffalsed.mm"
include "breqtrd.mm"
include "leadd2dd.mm"
include "recnd.mm"
include "addid1d.mm"
include "simprlr.mm"
include "ssun1.mm"
include "ad2antrr.mm"
include "iftrued.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "iftrue.mm"
include "3eqtr4d.mm"
include "breqtrrd.mm"
include "xrletrd.mm"
include "iffalse.mm"
include "leadd1dd.mm"
include "addid2d.mm"
include "ad3antrrr.mm"
include "eleq2d.mm"
include "wo.mm"
include "biorf.mm"
include "elun.mm"
include "syl6rbbr.mm"
include "bitrd.mm"
include "ifbid.mm"
include "eqtrd.mm"
include "pm2.61dan.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "ralrimi.mm"
include "nffv.mm"
include "fveq2.mm"
include "breq12d.mm"
include "cbvral.mm"
include "itg2uba.mm"
include "eqbrtrrd.mm"
include "adantrr.mm"
include "leaddsub2d.mm"
include "anassrs.mm"
include "expr.mm"
include "ralrimiva.mm"
include "resubcld.mm"
include "itg2leub.mm"
include "mpbird.mm"
include "lesubd.mm"
include "leaddsub.mm"
include "itg2cl.mm"
include "xrletri3.mm"
include "mpbir2and.mm"

theorem itg2split
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  assume itg2split.a: |- ( ph -> A e. dom vol )
  assume itg2split.b: |- ( ph -> B e. dom vol )
  assume itg2split.i: |- ( ph -> ( vol* ` ( A i^i B ) ) = 0 )
  assume itg2split.u: |- ( ph -> U = ( A u. B ) )
  assume itg2split.c: |- ( ( ph /\ x e. U ) -> C e. ( 0 [,] +oo ) )
  assume itg2split.f: |- F = ( x e. RR |-> if ( x e. A , C , 0 ) )
  assume itg2split.g: |- G = ( x e. RR |-> if ( x e. B , C , 0 ) )
  assume itg2split.h: |- H = ( x e. RR |-> if ( x e. U , C , 0 ) )
  assume itg2split.sf: |- ( ph -> ( S.2 ` F ) e. RR )
  assume itg2split.sg: |- ( ph -> ( S.2 ` G ) e. RR )

  disjoint ph x
  disjoint A x
  disjoint B x
  disjoint U x
  disjoint f g
  disjoint f y
  disjoint F f
  disjoint g y
  disjoint F g
  disjoint F y
  disjoint G f
  disjoint G g
  disjoint G y
  disjoint H f
  disjoint H g
  disjoint H y
  disjoint f x
  disjoint f ph
  disjoint g x
  disjoint g ph
  disjoint x y
  disjoint ph y
  disjoint A y
  disjoint B y
  assert |- ( ph -> ( S.2 ` H ) = ( ( S.2 ` F ) + ( S.2 ` G ) ) )

  proof
    wph
    cH
    citg2
    cfv
    #
    cF
    citg2
    cfv
    #
    cG
    citg2
    cfv
    #
    caddc
    co
    #
    wceq
    #
    @0
    @3
    cle
    wbr
    #
    @3
    @0
    cle
    wbr
    #
    wph
    vx
    cA
    cB
    cC
    cU
    cF
    cG
    cH
    itg2split.a
    itg2split.b
    itg2split.i
    itg2split.u
    itg2split.c
    itg2split.f
    itg2split.g
    itg2split.h
    itg2split.sf
    itg2split.sg
    itg2splitlem
    #
    wph
    @6
    @1
    @0
    @2
    cmin
    co
    #
    cle
    wbr
    #
    wph
    @9
    vf
    cv
    #
    cF
    cle
    cofr
    #
    wbr
    #
    @10
    citg1
    cfv
    #
    @8
    cle
    wbr
    #
    wi
    #
    vf
    citg1
    cdm
    #
    wral
    #
    wph
    @15
    vf
    @16
    wph
    @10
    @16
    wcel
    #
    @12
    @14
    wph
    @18
    @12
    wa
    #
    wa
    #
    @2
    @0
    @13
    wph
    @2
    cr
    wcel
    #
    @19
    itg2split.sg
    adantr
    wph
    @0
    cr
    wcel
    #
    @19
    wph
    cr
    cc0
    cpnf
    cicc
    co
    #
    cH
    wf
    #
    @3
    cr
    wcel
    @5
    @22
    wph
    vx
    cr
    vx
    cv
    #
    cU
    wcel
    #
    cC
    cc0
    cif
    #
    @23
    cH
    wph
    @25
    cr
    wcel
    #
    wa
    #
    @26
    cC
    cc0
    @23
    wph
    @26
    cC
    @23
    wcel
    #
    @28
    itg2split.c
    adantlr
    #
    cc0
    @23
    wcel
    #
    @29
    @26
    wn
    wa
    0e0iccpnf
    a1i
    ifclda
    #
    itg2split.h
    fmptd
    #
    wph
    @1
    @2
    itg2split.sf
    itg2split.sg
    readdcld
    #
    @7
    @3
    cH
    itg2lecl
    syl3anc
    #
    adantr
    #
    @18
    @13
    cr
    wcel
    #
    wph
    @12
    @10
    itg1cl
    ad2antrl
    #
    @20
    @2
    @0
    @13
    cmin
    co
    #
    cle
    wbr
    #
    vg
    cv
    #
    cG
    @11
    wbr
    #
    @42
    citg1
    cfv
    #
    @40
    cle
    wbr
    #
    wi
    #
    vg
    @16
    wral
    #
    @20
    @46
    vg
    @16
    @20
    @42
    @16
    wcel
    #
    @43
    @45
    wph
    @19
    @48
    @43
    wa
    #
    @45
    wph
    @19
    @49
    wa
    #
    wa
    #
    @13
    @44
    caddc
    co
    #
    @0
    cle
    wbr
    @45
    @51
    @10
    @42
    caddc
    cof
    co
    #
    citg1
    cfv
    @52
    @0
    cle
    @51
    @10
    @42
    wph
    @18
    @12
    @49
    simprll
    #
    wph
    @19
    @48
    @43
    simprrl
    #
    itg1add
    @51
    vy
    cA
    cB
    cin
    #
    cH
    @53
    wph
    @24
    @50
    @34
    adantr
    #
    @51
    @10
    @42
    @54
    @55
    i1fadd
    wph
    @56
    cr
    wss
    @50
    wph
    @56
    cA
    cr
    cA
    cB
    inss1
    wph
    cA
    cvol
    cdm
    wcel
    cA
    cr
    wss
    itg2split.a
    cA
    mblss
    syl
    syl5ss
    adantr
    wph
    @56
    covol
    cfv
    cc0
    wceq
    @50
    itg2split.i
    adantr
    @51
    vy
    cv
    #
    @53
    cfv
    #
    @58
    cH
    cfv
    #
    cle
    wbr
    #
    vy
    cr
    @56
    cdif
    #
    @51
    @25
    @53
    cfv
    #
    @25
    cH
    cfv
    #
    cle
    wbr
    #
    vx
    @62
    wral
    @61
    vy
    @62
    wral
    @51
    @65
    vx
    @62
    wph
    @50
    vx
    wph
    vx
    nfv
    @19
    @49
    vx
    @18
    @12
    vx
    @18
    vx
    nfv
    vx
    @10
    cF
    @11
    vx
    @10
    nfcv
    vx
    @11
    nfcv
    #
    vx
    cF
    vx
    cr
    @25
    cA
    wcel
    #
    cC
    cc0
    cif
    #
    cmpt
    #
    itg2split.f
    vx
    cr
    @68
    nfmpt1
    nfcxfr
    nfbr
    nfan
    @48
    @43
    vx
    @48
    vx
    nfv
    vx
    @42
    cG
    @11
    vx
    @42
    nfcv
    @66
    vx
    cG
    vx
    cr
    @25
    cB
    wcel
    #
    cC
    cc0
    cif
    #
    cmpt
    #
    itg2split.g
    vx
    cr
    @71
    nfmpt1
    nfcxfr
    nfbr
    nfan
    nfan
    nfan
    @51
    @25
    @62
    wcel
    #
    @65
    @51
    @73
    wa
    #
    @63
    @25
    @10
    cfv
    #
    @25
    @42
    cfv
    #
    caddc
    co
    #
    @64
    cle
    @73
    @51
    @28
    @63
    @77
    wceq
    @25
    cr
    @56
    eldifi
    #
    @51
    cr
    cr
    @75
    @76
    caddc
    cr
    @10
    @42
    cvv
    cvv
    @25
    @51
    cr
    cr
    @10
    wf
    #
    @10
    cr
    wfn
    #
    @51
    @18
    @79
    @54
    @10
    i1ff
    syl
    #
    cr
    cr
    @10
    ffn
    syl
    #
    @51
    cr
    cr
    @42
    wf
    #
    @42
    cr
    wfn
    #
    @51
    @48
    @83
    @55
    @42
    i1ff
    syl
    #
    cr
    cr
    @42
    ffn
    syl
    #
    cr
    cvv
    wcel
    #
    @51
    reex
    a1i
    #
    @88
    cr
    inidm
    @51
    @28
    wa
    #
    @75
    eqidd
    @89
    @76
    eqidd
    ofval
    sylan2
    @74
    @67
    @77
    @64
    cle
    wbr
    @74
    @67
    wa
    #
    @77
    @75
    @64
    @74
    @77
    cxr
    wcel
    #
    @67
    @74
    @77
    @74
    @75
    @76
    @51
    @79
    @28
    @75
    cr
    wcel
    #
    @73
    @81
    @78
    cr
    cr
    @25
    @10
    ffvelrn
    syl2an
    #
    @51
    @83
    @28
    @76
    cr
    wcel
    #
    @73
    @85
    @78
    cr
    cr
    @25
    @42
    ffvelrn
    syl2an
    #
    readdcld
    rexrd
    #
    adantr
    @90
    @75
    @74
    @92
    @67
    @93
    adantr
    #
    rexrd
    @74
    @64
    cxr
    wcel
    #
    @67
    @74
    @23
    cxr
    @64
    cc0
    cpnf
    iccssxr
    @51
    @24
    @28
    @64
    @23
    wcel
    @73
    @57
    @78
    cr
    @23
    @25
    cH
    ffvelrn
    syl2an
    sseldi
    #
    adantr
    @90
    @77
    @75
    cc0
    caddc
    co
    @75
    cle
    @90
    @76
    cc0
    @75
    @74
    @94
    @67
    @95
    adantr
    @90
    0red
    @97
    @90
    @76
    @71
    cc0
    cle
    @74
    @76
    @71
    cle
    wbr
    #
    @67
    @73
    @51
    @28
    @100
    @78
    @51
    @100
    vx
    cr
    @51
    @43
    @100
    vx
    cr
    wral
    #
    wph
    @19
    @48
    @43
    simprrr
    wph
    @50
    @84
    @43
    @101
    wb
    @86
    wph
    @84
    wa
    #
    vx
    cr
    @76
    @71
    cle
    @42
    cG
    cvv
    cvv
    @23
    @87
    @102
    reex
    a1i
    @102
    @28
    wa
    @25
    @42
    fvexd
    wph
    @28
    @71
    @23
    wcel
    @84
    @29
    @70
    cC
    cc0
    @23
    @29
    @70
    @26
    @30
    wph
    @70
    @26
    @28
    wph
    cB
    cU
    @25
    wph
    cA
    cB
    cun
    #
    cB
    cU
    cB
    cA
    ssun2
    itg2split.u
    syl5sseqr
    sselda
    adantlr
    @31
    syldan
    @32
    @29
    @70
    wn
    #
    wa
    0e0iccpnf
    a1i
    ifclda
    #
    adantlr
    @102
    @84
    @42
    vx
    cr
    @76
    cmpt
    wceq
    wph
    @84
    simpr
    vx
    cr
    @42
    dffn5
    sylib
    cG
    @72
    wceq
    @102
    itg2split.g
    a1i
    ofrfval2
    syldan
    mpbid
    r19.21bi
    sylan2
    #
    adantr
    @90
    @70
    cC
    cc0
    @74
    @67
    @104
    @74
    @67
    @70
    wa
    #
    wn
    @67
    @104
    wi
    @74
    @25
    @56
    wcel
    #
    @107
    @73
    @108
    wn
    @51
    @25
    cr
    @56
    eldifn
    adantl
    @25
    cA
    cB
    elin
    sylnib
    @67
    @70
    imnan
    sylibr
    imp
    iffalsed
    breqtrd
    leadd2dd
    @90
    @75
    @90
    @75
    @97
    recnd
    addid1d
    breqtrd
    @90
    @75
    @68
    @64
    cle
    @74
    @75
    @68
    cle
    wbr
    #
    @67
    @73
    @51
    @28
    @109
    @78
    @51
    @109
    vx
    cr
    @51
    @12
    @109
    vx
    cr
    wral
    #
    wph
    @18
    @12
    @49
    simprlr
    wph
    @50
    @80
    @12
    @110
    wb
    @82
    wph
    @80
    wa
    #
    vx
    cr
    @75
    @68
    cle
    @10
    cF
    cvv
    cvv
    @23
    @87
    @111
    reex
    a1i
    @111
    @28
    wa
    @25
    @10
    fvexd
    wph
    @28
    @68
    @23
    wcel
    @80
    @29
    @67
    cC
    cc0
    @23
    @29
    @67
    @26
    @30
    wph
    @67
    @26
    @28
    wph
    cA
    cU
    @25
    wph
    @103
    cA
    cU
    cA
    cB
    ssun1
    itg2split.u
    syl5sseqr
    #
    sselda
    adantlr
    @31
    syldan
    @32
    @29
    @67
    wn
    #
    wa
    0e0iccpnf
    a1i
    ifclda
    #
    adantlr
    @111
    @80
    @10
    vx
    cr
    @75
    cmpt
    wceq
    wph
    @80
    simpr
    vx
    cr
    @10
    dffn5
    sylib
    cF
    @69
    wceq
    @111
    itg2split.f
    a1i
    ofrfval2
    syldan
    mpbid
    r19.21bi
    sylan2
    #
    adantr
    @90
    @27
    cC
    @64
    @68
    @90
    @26
    cC
    cc0
    @74
    cA
    cU
    @25
    wph
    cA
    cU
    wss
    @50
    @73
    @112
    ad2antrr
    sselda
    iftrued
    @74
    @64
    @27
    wceq
    #
    @67
    @73
    @51
    @28
    @116
    @78
    @89
    @28
    @27
    @23
    wcel
    #
    @116
    @51
    @28
    simpr
    wph
    @28
    @117
    @50
    @33
    adantlr
    vx
    cr
    @27
    @23
    cH
    itg2split.h
    fvmpt2
    syl2anc
    sylan2
    #
    adantr
    @67
    @68
    cC
    wceq
    @74
    @67
    cC
    cc0
    iftrue
    adantl
    3eqtr4d
    breqtrrd
    xrletrd
    @74
    @113
    wa
    #
    @77
    @76
    @64
    @74
    @91
    @113
    @96
    adantr
    @119
    @76
    @74
    @94
    @113
    @95
    adantr
    #
    rexrd
    @74
    @98
    @113
    @99
    adantr
    @119
    @77
    cc0
    @76
    caddc
    co
    @76
    cle
    @119
    @75
    cc0
    @76
    @74
    @92
    @113
    @93
    adantr
    @119
    0red
    @120
    @119
    @75
    @68
    cc0
    cle
    @74
    @109
    @113
    @115
    adantr
    @113
    @68
    cc0
    wceq
    @74
    @67
    cC
    cc0
    iffalse
    adantl
    breqtrd
    leadd1dd
    @119
    @76
    @119
    @76
    @120
    recnd
    addid2d
    breqtrd
    @119
    @76
    @71
    @64
    cle
    @74
    @100
    @113
    @106
    adantr
    @119
    @64
    @27
    @71
    @74
    @116
    @113
    @118
    adantr
    @119
    @26
    @70
    cC
    cc0
    @119
    @26
    @25
    @103
    wcel
    #
    @70
    @119
    cU
    @103
    @25
    wph
    cU
    @103
    wceq
    @50
    @73
    @113
    itg2split.u
    ad3antrrr
    eleq2d
    @113
    @121
    @70
    wb
    @74
    @113
    @70
    @67
    @70
    wo
    @121
    @67
    @70
    biorf
    @25
    cA
    cB
    elun
    syl6rbbr
    adantl
    bitrd
    ifbid
    eqtrd
    breqtrrd
    xrletrd
    pm2.61dan
    eqbrtrd
    ex
    ralrimi
    @65
    @61
    vx
    vy
    @62
    @65
    vy
    nfv
    vx
    @59
    @60
    cle
    vx
    @59
    nfcv
    vx
    cle
    nfcv
    vx
    @58
    cH
    vx
    cH
    vx
    cr
    @27
    cmpt
    itg2split.h
    vx
    cr
    @27
    nfmpt1
    nfcxfr
    vx
    @58
    nfcv
    nffv
    nfbr
    @25
    @58
    wceq
    @63
    @59
    @64
    @60
    cle
    @25
    @58
    @53
    fveq2
    @25
    @58
    cH
    fveq2
    breq12d
    cbvral
    sylib
    r19.21bi
    itg2uba
    eqbrtrrd
    @51
    @13
    @44
    @0
    wph
    @19
    @38
    @49
    @39
    adantrr
    @51
    @48
    @44
    cr
    wcel
    @55
    @42
    itg1cl
    syl
    wph
    @22
    @50
    @36
    adantr
    leaddsub2d
    mpbid
    anassrs
    expr
    ralrimiva
    @20
    cr
    @23
    cG
    wf
    #
    @40
    cxr
    wcel
    @41
    @47
    wb
    wph
    @122
    @19
    wph
    vx
    cr
    @71
    @23
    cG
    @105
    itg2split.g
    fmptd
    adantr
    @20
    @40
    @20
    @0
    @13
    @37
    @39
    resubcld
    rexrd
    @40
    vg
    cG
    itg2leub
    syl2anc
    mpbird
    lesubd
    expr
    ralrimiva
    wph
    cr
    @23
    cF
    wf
    @8
    cxr
    wcel
    @9
    @17
    wb
    wph
    vx
    cr
    @68
    @23
    cF
    @114
    itg2split.f
    fmptd
    wph
    @8
    wph
    @0
    @2
    @36
    itg2split.sg
    resubcld
    rexrd
    @8
    vf
    cF
    itg2leub
    syl2anc
    mpbird
    wph
    @1
    cr
    wcel
    @21
    @22
    @6
    @9
    wb
    itg2split.sf
    itg2split.sg
    @36
    @1
    @2
    @0
    leaddsub
    syl3anc
    mpbird
    wph
    @0
    cxr
    wcel
    #
    @3
    cxr
    wcel
    @4
    @5
    @6
    wa
    wb
    wph
    @24
    @123
    @34
    cH
    itg2cl
    syl
    wph
    @3
    @35
    rexrd
    @0
    @3
    xrletri3
    syl2anc
    mpbir2and
end
