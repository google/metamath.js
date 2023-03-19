include "citg2.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cofr.mm"
include "citg1.mm"
include "wi.mm"
include "cdm.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "simprl.mm"
include "itg1cl.mm"
include "syl.mm"
include "cvol.mm"
include "adantr.mm"
include "eqid.mm"
include "i1fres.mm"
include "syl2anc.mm"
include "readdcld.mm"
include "cin.mm"
include "wss.mm"
include "inss1.mm"
include "mblss.mm"
include "syl5ss.mm"
include "covol.mm"
include "wceq.mm"
include "cof.mm"
include "cvv.mm"
include "reex.mm"
include "a1i.mm"
include "fvex.mm"
include "c0ex.mm"
include "ifex.mm"
include "eqidd.mm"
include "offval2.mm"
include "i1fadd.mm"
include "eqeltrrd.mm"
include "cdif.mm"
include "wf.mm"
include "i1ff.mm"
include "eldifi.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "leidd.mm"
include "iftrue.mm"
include "adantl.mm"
include "wn.mm"
include "eldifn.mm"
include "elin.mm"
include "sylnib.mm"
include "imnan.mm"
include "sylibr.mm"
include "imp.mm"
include "iffalse.mm"
include "oveq12d.mm"
include "cc.mm"
include "recnd.mm"
include "addid1d.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "ad2antrr.mm"
include "wo.mm"
include "cun.mm"
include "eleq2d.mm"
include "elun.mm"
include "syl6bb.mm"
include "notbid.mm"
include "ioran.mm"
include "biimpar.mm"
include "simprr.mm"
include "wfn.mm"
include "ffn.mm"
include "cpnf.mm"
include "cicc.mm"
include "adantlr.mm"
include "0e0iccpnf.mm"
include "ifclda.mm"
include "fmptd.mm"
include "inidm.mm"
include "ofrfval.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "sylan2.mm"
include "eldif.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfeq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "cid.mm"
include "fvmpt2i.mm"
include "fveq2d.mm"
include "0cn.mm"
include "fvi.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "sylan9eq.mm"
include "sylbi.mm"
include "vtoclgaf.mm"
include "sylbir.mm"
include "sylan.mm"
include "breqtrd.mm"
include "syldan.mm"
include "anassrs.mm"
include "pm2.61dan.mm"
include "oveq1d.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "addid2d.mm"
include "eleq1.mm"
include "ifbieq1d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "itg1lea.mm"
include "itg1add.mm"
include "eqtr3d.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "sselda.mm"
include "nfv.mm"
include "nfbr.mm"
include "nfan.mm"
include "feqmptd.mm"
include "ofrfval2.mm"
include "biimpd.mm"
include "impr.mm"
include "iftrued.mm"
include "3brtr4d.mm"
include "0le0.mm"
include "a1d.mm"
include "ralrimi.mm"
include "wb.mm"
include "mpbird.mm"
include "itg2ub.mm"
include "syl3anc.mm"
include "ssun2.mm"
include "le2addd.mm"
include "letrd.mm"
include "expr.mm"
include "ralrimiva.mm"
include "cxr.mm"
include "rexrd.mm"
include "itg2leub.mm"

theorem itg2splitlem
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
  assert |- ( ph -> ( S.2 ` H ) <_ ( ( S.2 ` F ) + ( S.2 ` G ) ) )

  proof
    wph
    cH
    citg2
    cfv
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
    cle
    wbr
    #
    vf
    cv
    #
    cH
    cle
    cofr
    #
    wbr
    #
    @4
    citg1
    cfv
    #
    @2
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
    @9
    vf
    @10
    wph
    @4
    @10
    wcel
    #
    @6
    @8
    wph
    @12
    @6
    wa
    #
    wa
    #
    @7
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    @15
    @4
    cfv
    #
    cc0
    cif
    #
    cmpt
    #
    citg1
    cfv
    #
    vx
    cr
    @15
    cB
    wcel
    #
    @17
    cc0
    cif
    #
    cmpt
    #
    citg1
    cfv
    #
    caddc
    co
    #
    @2
    @14
    @12
    @7
    cr
    wcel
    wph
    @12
    @6
    simprl
    #
    @4
    itg1cl
    syl
    @14
    @20
    @24
    @14
    @19
    @10
    wcel
    #
    @20
    cr
    wcel
    @14
    @12
    cA
    cvol
    cdm
    #
    wcel
    #
    @27
    @26
    wph
    @29
    @13
    itg2split.a
    adantr
    #
    vx
    cA
    @4
    @19
    @19
    eqid
    i1fres
    syl2anc
    #
    @19
    itg1cl
    syl
    #
    @14
    @23
    @10
    wcel
    #
    @24
    cr
    wcel
    @14
    @12
    cB
    @28
    wcel
    #
    @33
    @26
    wph
    @34
    @13
    itg2split.b
    adantr
    #
    vx
    cB
    @4
    @23
    @23
    eqid
    i1fres
    syl2anc
    #
    @23
    itg1cl
    syl
    #
    readdcld
    wph
    @2
    cr
    wcel
    @13
    wph
    @0
    @1
    itg2split.sf
    itg2split.sg
    readdcld
    #
    adantr
    @14
    @7
    vx
    cr
    @18
    @22
    caddc
    co
    #
    cmpt
    #
    citg1
    cfv
    #
    @25
    cle
    @14
    vy
    cA
    cB
    cin
    #
    @4
    @40
    @26
    wph
    @42
    cr
    wss
    @13
    wph
    @42
    cA
    cr
    cA
    cB
    inss1
    wph
    @29
    cA
    cr
    wss
    #
    itg2split.a
    cA
    mblss
    #
    syl
    syl5ss
    adantr
    wph
    @42
    covol
    cfv
    cc0
    wceq
    @13
    itg2split.i
    adantr
    @14
    @19
    @23
    caddc
    cof
    co
    #
    @40
    @10
    wph
    @45
    @40
    wceq
    @13
    wph
    vx
    cr
    @18
    @22
    caddc
    @19
    @23
    cvv
    cvv
    cvv
    cr
    cvv
    wcel
    #
    wph
    reex
    a1i
    #
    @18
    cvv
    wcel
    wph
    @15
    cr
    wcel
    #
    wa
    #
    @16
    @17
    cc0
    @15
    @4
    fvex
    #
    c0ex
    ifex
    a1i
    #
    @22
    cvv
    wcel
    @49
    @21
    @17
    cc0
    @50
    c0ex
    ifex
    a1i
    #
    wph
    @19
    eqidd
    #
    wph
    @23
    eqidd
    #
    offval2
    adantr
    #
    @14
    @19
    @23
    @31
    @36
    i1fadd
    eqeltrrd
    @14
    vy
    cv
    #
    cr
    @42
    cdif
    wcel
    #
    wa
    #
    @56
    @4
    cfv
    #
    @56
    cA
    wcel
    #
    @59
    cc0
    cif
    #
    @56
    cB
    wcel
    #
    @59
    cc0
    cif
    #
    caddc
    co
    #
    @56
    @40
    cfv
    #
    cle
    @58
    @60
    @59
    @64
    cle
    wbr
    @58
    @60
    wa
    #
    @59
    @59
    @64
    cle
    @58
    @59
    @59
    cle
    wbr
    #
    @60
    @58
    @59
    @14
    cr
    cr
    @4
    wf
    #
    @56
    cr
    wcel
    #
    @59
    cr
    wcel
    #
    @57
    @14
    @12
    @68
    @26
    @4
    i1ff
    #
    syl
    #
    @56
    cr
    @42
    eldifi
    #
    cr
    cr
    @56
    @4
    ffvelrn
    syl2an
    #
    leidd
    #
    adantr
    @66
    @64
    @59
    cc0
    caddc
    co
    @59
    @66
    @61
    @59
    @63
    cc0
    caddc
    @60
    @61
    @59
    wceq
    @58
    @60
    @59
    cc0
    iftrue
    adantl
    @66
    @62
    wn
    #
    @63
    cc0
    wceq
    #
    @58
    @60
    @76
    @58
    @60
    @62
    wa
    #
    wn
    @60
    @76
    wi
    @58
    @56
    @42
    wcel
    #
    @78
    @57
    @79
    wn
    @14
    @56
    cr
    @42
    eldifn
    adantl
    @56
    cA
    cB
    elin
    sylnib
    @60
    @62
    imnan
    sylibr
    imp
    @62
    @59
    cc0
    iffalse
    #
    syl
    oveq12d
    @66
    @59
    @58
    @59
    cc
    wcel
    @60
    @58
    @59
    @74
    recnd
    adantr
    addid1d
    eqtrd
    breqtrrd
    @58
    @60
    wn
    #
    wa
    #
    @59
    @63
    @64
    cle
    @82
    @62
    @59
    @63
    cle
    wbr
    @82
    @62
    wa
    @59
    @59
    @63
    cle
    @58
    @67
    @81
    @62
    @75
    ad2antrr
    @62
    @63
    @59
    wceq
    @82
    @62
    @59
    cc0
    iftrue
    adantl
    breqtrrd
    @82
    @76
    wa
    @59
    cc0
    @63
    cle
    @58
    @81
    @76
    @59
    cc0
    cle
    wbr
    #
    @58
    @81
    @76
    wa
    #
    @56
    cU
    wcel
    #
    wn
    #
    @83
    @58
    @86
    @84
    @58
    @86
    @60
    @62
    wo
    #
    wn
    @84
    @58
    @85
    @87
    @58
    @85
    @56
    cA
    cB
    cun
    #
    wcel
    @87
    @58
    cU
    @88
    @56
    wph
    cU
    @88
    wceq
    @13
    @57
    itg2split.u
    ad2antrr
    eleq2d
    @56
    cA
    cB
    elun
    syl6bb
    notbid
    @60
    @62
    ioran
    syl6bb
    biimpar
    @58
    @86
    wa
    @59
    @56
    cH
    cfv
    #
    cc0
    cle
    @58
    @59
    @89
    cle
    wbr
    #
    @86
    @57
    @14
    @69
    @90
    @73
    @14
    @90
    vy
    cr
    @14
    @6
    @90
    vy
    cr
    wral
    wph
    @12
    @6
    simprr
    @14
    vy
    cr
    cr
    @59
    @89
    cle
    cr
    @4
    cH
    cvv
    cvv
    @14
    @68
    @4
    cr
    wfn
    @72
    cr
    cr
    @4
    ffn
    syl
    wph
    cH
    cr
    wfn
    #
    @13
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
    @91
    wph
    vx
    cr
    @15
    cU
    wcel
    #
    cC
    cc0
    cif
    #
    @92
    cH
    @49
    @94
    cC
    cc0
    @92
    wph
    @94
    cC
    @92
    wcel
    #
    @48
    itg2split.c
    adantlr
    #
    cc0
    @92
    wcel
    #
    @49
    @94
    wn
    #
    wa
    0e0iccpnf
    a1i
    ifclda
    #
    itg2split.h
    fmptd
    #
    cr
    @92
    cH
    ffn
    syl
    adantr
    @46
    @14
    reex
    a1i
    #
    @102
    cr
    inidm
    @14
    @69
    wa
    #
    @59
    eqidd
    @103
    @89
    eqidd
    ofrfval
    mpbid
    r19.21bi
    sylan2
    adantr
    @58
    @69
    @86
    @89
    cc0
    wceq
    #
    @57
    @69
    @14
    @73
    adantl
    #
    @69
    @86
    wa
    @56
    cr
    cU
    cdif
    #
    wcel
    @104
    @56
    cr
    cU
    eldif
    @15
    cH
    cfv
    #
    cc0
    wceq
    #
    @104
    vx
    @56
    @106
    vx
    @56
    nfcv
    #
    vx
    @89
    cc0
    vx
    @56
    cH
    vx
    cH
    vx
    cr
    @95
    cmpt
    #
    itg2split.h
    vx
    cr
    @95
    nfmpt1
    nfcxfr
    #
    @109
    nffv
    nfeq1
    @15
    @56
    wceq
    #
    @107
    @89
    cc0
    @15
    @56
    cH
    fveq2
    eqeq1d
    @15
    @106
    wcel
    @48
    @99
    wa
    @108
    @15
    cr
    cU
    eldif
    @48
    @99
    @107
    @95
    cid
    cfv
    #
    cc0
    vx
    cr
    @95
    cH
    itg2split.h
    fvmpt2i
    @99
    @113
    cc0
    cid
    cfv
    #
    cc0
    @99
    @95
    cc0
    cid
    @94
    cC
    cc0
    iffalse
    fveq2d
    cc0
    cc
    wcel
    @114
    cc0
    wceq
    0cn
    cc0
    cc
    fvi
    ax-mp
    syl6eq
    sylan9eq
    sylbi
    vtoclgaf
    sylbir
    sylan
    breqtrd
    syldan
    anassrs
    @76
    @77
    @82
    @80
    adantl
    breqtrrd
    pm2.61dan
    @82
    @64
    cc0
    @63
    caddc
    co
    @63
    @82
    @61
    cc0
    @63
    caddc
    @81
    @61
    cc0
    wceq
    @58
    @60
    @59
    cc0
    iffalse
    adantl
    oveq1d
    @82
    @63
    @58
    @63
    cc
    wcel
    @81
    @58
    @63
    @58
    @70
    cc0
    cr
    wcel
    @63
    cr
    wcel
    @74
    0re
    @62
    @59
    cc0
    cr
    ifcl
    sylancl
    recnd
    adantr
    addid2d
    eqtrd
    breqtrrd
    pm2.61dan
    @58
    @69
    @65
    @64
    wceq
    @105
    vx
    @56
    @39
    @64
    cr
    @40
    @112
    @18
    @61
    @22
    @63
    caddc
    @112
    @16
    @60
    @17
    @59
    cc0
    @15
    @56
    cA
    eleq1
    @15
    @56
    @4
    fveq2
    #
    ifbieq1d
    @112
    @21
    @62
    @17
    @59
    cc0
    @15
    @56
    cB
    eleq1
    @115
    ifbieq1d
    oveq12d
    @40
    eqid
    @61
    @63
    caddc
    ovex
    fvmpt
    syl
    breqtrrd
    itg1lea
    @14
    @45
    citg1
    cfv
    @41
    @25
    @14
    @45
    @40
    citg1
    @55
    fveq2d
    @14
    @19
    @23
    @31
    @36
    itg1add
    eqtr3d
    breqtrd
    @14
    @20
    @24
    @0
    @1
    @32
    @37
    wph
    @0
    cr
    wcel
    @13
    itg2split.sf
    adantr
    wph
    @1
    cr
    wcel
    @13
    itg2split.sg
    adantr
    @14
    cr
    @92
    cF
    wf
    #
    @27
    @19
    cF
    @5
    wbr
    #
    @20
    @0
    cle
    wbr
    wph
    @116
    @13
    wph
    vx
    cr
    @16
    cC
    cc0
    cif
    #
    @92
    cF
    @49
    @16
    cC
    cc0
    @92
    @49
    @16
    @94
    @96
    wph
    @16
    @94
    @48
    wph
    cA
    cU
    @15
    wph
    @88
    cA
    cU
    cA
    cB
    ssun1
    itg2split.u
    syl5sseqr
    sselda
    #
    adantlr
    @97
    syldan
    @98
    @49
    @16
    wn
    #
    wa
    0e0iccpnf
    a1i
    ifclda
    #
    itg2split.f
    fmptd
    adantr
    @31
    @14
    @117
    @18
    @118
    cle
    wbr
    #
    vx
    cr
    wral
    #
    @14
    @122
    vx
    cr
    wph
    @13
    vx
    wph
    vx
    nfv
    @12
    @6
    vx
    @12
    vx
    nfv
    vx
    @4
    cH
    @5
    vx
    @4
    nfcv
    vx
    @5
    nfcv
    @111
    nfbr
    nfan
    nfan
    #
    @14
    @122
    @48
    @14
    @16
    @122
    @14
    @16
    wa
    #
    @17
    cC
    @18
    @118
    cle
    @125
    @17
    @95
    cC
    cle
    @14
    @16
    @48
    @17
    @95
    cle
    wbr
    #
    @14
    cA
    cr
    @15
    @14
    @29
    @43
    @30
    @44
    syl
    sselda
    @14
    @126
    vx
    cr
    wph
    @12
    @6
    @126
    vx
    cr
    wral
    #
    wph
    @12
    wa
    #
    @6
    @127
    @128
    vx
    cr
    @17
    @95
    cle
    @4
    cH
    cvv
    cvv
    @92
    @46
    @128
    reex
    a1i
    @17
    cvv
    wcel
    @128
    @48
    wa
    @50
    a1i
    wph
    @48
    @95
    @92
    wcel
    @12
    @100
    adantlr
    @128
    vx
    cr
    cr
    @4
    @12
    @68
    wph
    @71
    adantl
    feqmptd
    cH
    @110
    wceq
    @128
    itg2split.h
    a1i
    ofrfval2
    biimpd
    impr
    r19.21bi
    #
    syldan
    @125
    @94
    cC
    cc0
    wph
    @16
    @94
    @13
    @119
    adantlr
    iftrued
    breqtrd
    @16
    @18
    @17
    wceq
    @14
    @16
    @17
    cc0
    iftrue
    adantl
    @16
    @118
    cC
    wceq
    @14
    @16
    cC
    cc0
    iftrue
    adantl
    3brtr4d
    @120
    @122
    @14
    @120
    cc0
    cc0
    @18
    @118
    cle
    cc0
    cc0
    cle
    wbr
    #
    @120
    0le0
    a1i
    @16
    @17
    cc0
    iffalse
    @16
    cC
    cc0
    iffalse
    3brtr4d
    adantl
    pm2.61dan
    a1d
    ralrimi
    wph
    @117
    @123
    wb
    @13
    wph
    vx
    cr
    @18
    @118
    cle
    @19
    cF
    cvv
    cvv
    @92
    @47
    @51
    @121
    @53
    cF
    vx
    cr
    @118
    cmpt
    wceq
    wph
    itg2split.f
    a1i
    ofrfval2
    adantr
    mpbird
    cF
    @19
    itg2ub
    syl3anc
    @14
    cr
    @92
    cG
    wf
    #
    @33
    @23
    cG
    @5
    wbr
    #
    @24
    @1
    cle
    wbr
    wph
    @131
    @13
    wph
    vx
    cr
    @21
    cC
    cc0
    cif
    #
    @92
    cG
    @49
    @21
    cC
    cc0
    @92
    @49
    @21
    @94
    @96
    wph
    @21
    @94
    @48
    wph
    cB
    cU
    @15
    wph
    @88
    cB
    cU
    cB
    cA
    ssun2
    itg2split.u
    syl5sseqr
    sselda
    #
    adantlr
    @97
    syldan
    @98
    @49
    @21
    wn
    #
    wa
    0e0iccpnf
    a1i
    ifclda
    #
    itg2split.g
    fmptd
    adantr
    @36
    @14
    @132
    @22
    @133
    cle
    wbr
    #
    vx
    cr
    wral
    #
    @14
    @137
    vx
    cr
    @124
    @14
    @137
    @48
    @14
    @21
    @137
    @14
    @21
    wa
    #
    @17
    cC
    @22
    @133
    cle
    @139
    @17
    @95
    cC
    cle
    @14
    @21
    @48
    @126
    @14
    cB
    cr
    @15
    @14
    @34
    cB
    cr
    wss
    @35
    cB
    mblss
    syl
    sselda
    @129
    syldan
    @139
    @94
    cC
    cc0
    wph
    @21
    @94
    @13
    @134
    adantlr
    iftrued
    breqtrd
    @21
    @22
    @17
    wceq
    @14
    @21
    @17
    cc0
    iftrue
    adantl
    @21
    @133
    cC
    wceq
    @14
    @21
    cC
    cc0
    iftrue
    adantl
    3brtr4d
    @135
    @137
    @14
    @135
    cc0
    cc0
    @22
    @133
    cle
    @130
    @135
    0le0
    a1i
    @21
    @17
    cc0
    iffalse
    @21
    cC
    cc0
    iffalse
    3brtr4d
    adantl
    pm2.61dan
    a1d
    ralrimi
    wph
    @132
    @138
    wb
    @13
    wph
    vx
    cr
    @22
    @133
    cle
    @23
    cG
    cvv
    cvv
    @92
    @47
    @52
    @136
    @54
    cG
    vx
    cr
    @133
    cmpt
    wceq
    wph
    itg2split.g
    a1i
    ofrfval2
    adantr
    mpbird
    cG
    @23
    itg2ub
    syl3anc
    le2addd
    letrd
    expr
    ralrimiva
    wph
    @93
    @2
    cxr
    wcel
    @3
    @11
    wb
    @101
    wph
    @2
    @38
    rexrd
    @2
    vf
    cH
    itg2leub
    syl2anc
    mpbird
end
