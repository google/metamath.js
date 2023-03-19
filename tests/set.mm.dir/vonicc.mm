include "c0.mm"
include "wceq.mm"
include "cvoln.mm"
include "cfv.mm"
include "co.mm"
include "wa.mm"
include "cc0.mm"
include "cr.mm"
include "wf.mm"
include "adantr.mm"
include "wb.mm"
include "feq2.mm"
include "adantl.mm"
include "mpbid.mm"
include "hoidmv0val.mm"
include "eqcomd.mm"
include "cv.mm"
include "cicc.mm"
include "cixp.mm"
include "fveq2.mm"
include "a1i.mm"
include "ixpeq1.mm"
include "eqtrd.mm"
include "fveq12d.mm"
include "cdm.mm"
include "cfn.mm"
include "wcel.mm"
include "0fin.mm"
include "eqid.mm"
include "iccvonmbl.mm"
include "von0val.mm"
include "oveqd.mm"
include "3eqtr4d.mm"
include "wn.mm"
include "wne.mm"
include "neqne.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cmin.mm"
include "cprod.mm"
include "cico.mm"
include "cvol.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "cif.mm"
include "ffvelrnda.mm"
include "volico2.mm"
include "syl2anc.mm"
include "ad4ant14.mm"
include "rspa.mm"
include "iftrued.mm"
include "adantll.mm"
include "ex.mm"
include "ralrimi.mm"
include "prodeq2d.mm"
include "breq12d.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "cn.mm"
include "c1.mm"
include "cdiv.mm"
include "caddc.mm"
include "cmpt.mm"
include "simpr.mm"
include "sylanbr.mm"
include "oveq1d.mm"
include "cbvmptv.mm"
include "mpteq2i.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "mpteq2dv.mm"
include "eqtri.mm"
include "fveq1d.mm"
include "ixpeq2dv.mm"
include "vonicclem2.mm"
include "syldan.mm"
include "hoidmvn0val.mm"
include "clt.mm"
include "wrex.mm"
include "rexnal.mm"
include "bicomi.mm"
include "wi.mm"
include "ltnled.mm"
include "mpbird.mm"
include "reximdva.mm"
include "mpd.mm"
include "adantlr.mm"
include "nfcv.mm"
include "nfixp1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "cmap.mm"
include "cmpt2.mm"
include "nfcprod1.mm"
include "nfif.mm"
include "nfmpt2.mm"
include "nfmpt.mm"
include "nfov.mm"
include "nfeq.mm"
include "w3a.mm"
include "vonmea.mm"
include "mea0.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "cxr.mm"
include "ressxr.mm"
include "sseldi.mm"
include "icc0.mm"
include "3adant3.mm"
include "rspe.mm"
include "ixp0.mm"
include "syl.mm"
include "fveq2d.mm"
include "ne0i.mm"
include "eleq1.mm"
include "3anbi23d.mm"
include "imbi1d.mm"
include "cc.mm"
include "volicore.mm"
include "recnd.mm"
include "3ad2antl1.mm"
include "oveq12d.mm"
include "iffalsed.mm"
include "fprodeq0g.mm"
include "chvarv.mm"
include "3exp.mm"
include "rexlimd.mm"
include "imp.mm"
include "pm2.61dan.mm"

theorem vonicc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cI: class I
  let cL: class L
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let vm: setvar m
  assume vonicc.x: |- ( ph -> X e. Fin )
  assume vonicc.a: |- ( ph -> A : X --> RR )
  assume vonicc.b: |- ( ph -> B : X --> RR )
  assume vonicc.i: |- I = X_ k e. X ( ( A ` k ) [,] ( B ` k ) )
  assume vonicc.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )

  disjoint A a
  disjoint A b
  disjoint A k
  disjoint a b
  disjoint a k
  disjoint b k
  disjoint B a
  disjoint B b
  disjoint B k
  disjoint X a
  disjoint X b
  disjoint X k
  disjoint X x
  disjoint a x
  disjoint b x
  disjoint k x
  disjoint a ph
  disjoint b ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint A i
  disjoint A j
  disjoint A n
  disjoint i j
  disjoint i k
  disjoint i n
  disjoint j k
  disjoint j n
  disjoint k n
  disjoint B i
  disjoint B j
  disjoint B m
  disjoint B n
  disjoint i m
  disjoint j m
  disjoint k m
  disjoint m n
  disjoint I n
  disjoint X i
  disjoint X j
  disjoint X m
  disjoint X n
  disjoint j ph
  disjoint n ph
  assert |- ( ph -> ( ( voln ` X ) ` I ) = ( A ( L ` X ) B ) )

  proof
    wph
    cX
    c0
    wceq
    #
    cI
    cX
    cvoln
    cfv
    #
    cfv
    #
    cA
    cB
    cX
    cL
    cfv
    #
    co
    #
    wceq
    #
    wph
    @0
    wa
    #
    cc0
    cA
    cB
    c0
    cL
    cfv
    #
    co
    #
    @2
    @4
    @6
    @8
    cc0
    @6
    vx
    cA
    cB
    vk
    cL
    va
    vb
    vonicc.l
    @6
    cX
    cr
    cA
    wf
    #
    c0
    cr
    cA
    wf
    #
    wph
    @9
    @0
    vonicc.a
    adantr
    @0
    @9
    @10
    wb
    wph
    cX
    c0
    cr
    cA
    feq2
    adantl
    mpbid
    #
    @6
    cX
    cr
    cB
    wf
    #
    c0
    cr
    cB
    wf
    #
    wph
    @12
    @0
    vonicc.b
    adantr
    @0
    @12
    @13
    wb
    wph
    cX
    c0
    cr
    cB
    feq2
    adantl
    mpbid
    #
    hoidmv0val
    eqcomd
    @6
    @2
    vk
    c0
    vk
    cv
    #
    cA
    cfv
    #
    @15
    cB
    cfv
    #
    cicc
    co
    #
    cixp
    #
    c0
    cvoln
    cfv
    #
    cfv
    #
    cc0
    @0
    @2
    @21
    wceq
    wph
    @0
    cI
    @19
    @1
    @20
    cX
    c0
    cvoln
    fveq2
    @0
    cI
    vk
    cX
    @18
    cixp
    #
    @19
    cI
    @22
    wceq
    #
    @0
    vonicc.i
    a1i
    vk
    cX
    c0
    @18
    ixpeq1
    eqtrd
    fveq12d
    adantl
    @6
    @19
    @6
    cA
    cB
    @20
    cdm
    #
    vk
    c0
    c0
    cfn
    wcel
    @6
    0fin
    a1i
    @24
    eqid
    @11
    @14
    iccvonmbl
    von0val
    eqtrd
    @0
    @4
    @8
    wceq
    wph
    @0
    @3
    @7
    cA
    cB
    cX
    c0
    cL
    fveq2
    oveqd
    adantl
    3eqtr4d
    wph
    @0
    wn
    #
    cX
    c0
    wne
    #
    @5
    @25
    @26
    wph
    cX
    c0
    neqne
    adantl
    wph
    @26
    wa
    #
    @16
    @17
    cle
    wbr
    #
    vk
    cX
    wral
    #
    @5
    @27
    @29
    wa
    #
    cX
    @17
    @16
    cmin
    co
    #
    vk
    cprod
    #
    cX
    @16
    @17
    cico
    co
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    @2
    @4
    @30
    @35
    @32
    @30
    cX
    @34
    @31
    vk
    @30
    @34
    @31
    wceq
    #
    vk
    cX
    @27
    @29
    vk
    @27
    vk
    nfv
    #
    @28
    vk
    cX
    nfra1
    nfan
    @30
    @15
    cX
    wcel
    #
    @36
    @30
    @38
    wa
    @34
    @28
    @31
    cc0
    cif
    #
    @31
    wph
    @38
    @34
    @39
    wceq
    #
    @26
    @29
    wph
    @38
    wa
    #
    @16
    cr
    wcel
    #
    @17
    cr
    wcel
    #
    @40
    wph
    cX
    cr
    @15
    cA
    vonicc.a
    ffvelrnda
    #
    wph
    cX
    cr
    @15
    cB
    vonicc.b
    ffvelrnda
    #
    @16
    @17
    volico2
    syl2anc
    ad4ant14
    @29
    @38
    @39
    @31
    wceq
    @27
    @29
    @38
    wa
    @28
    @31
    cc0
    @28
    vk
    cX
    rspa
    #
    iftrued
    adantll
    eqtrd
    ex
    ralrimi
    prodeq2d
    eqcomd
    @27
    @29
    vj
    cv
    #
    cA
    cfv
    #
    @47
    cB
    cfv
    #
    cle
    wbr
    #
    vj
    cX
    wral
    #
    @2
    @32
    wceq
    @29
    @51
    @27
    @29
    @51
    @28
    @50
    vk
    vj
    cX
    @15
    @47
    wceq
    #
    @16
    @48
    @17
    @49
    cle
    @15
    @47
    cA
    fveq2
    #
    @15
    @47
    cB
    fveq2
    #
    breq12d
    cbvralv
    #
    biimpi
    adantl
    @27
    @51
    wa
    cA
    cB
    vm
    cn
    vj
    cX
    @49
    c1
    vm
    cv
    #
    cdiv
    co
    #
    caddc
    co
    #
    cmpt
    #
    cmpt
    #
    vi
    cn
    vk
    cX
    @16
    @15
    vi
    cv
    #
    @60
    cfv
    #
    cfv
    #
    cico
    co
    #
    cixp
    #
    cmpt
    vk
    vn
    cI
    cX
    @27
    cX
    cfn
    wcel
    #
    @51
    wph
    @66
    @26
    vonicc.x
    adantr
    #
    adantr
    @27
    @9
    @51
    wph
    @9
    @26
    vonicc.a
    adantr
    #
    adantr
    @27
    @12
    @51
    wph
    @12
    @26
    vonicc.b
    adantr
    #
    adantr
    @27
    @26
    @51
    wph
    @26
    simpr
    #
    adantr
    @51
    @38
    @28
    @27
    @51
    @29
    @38
    @28
    @55
    @46
    sylanbr
    adantll
    vonicc.i
    @60
    vm
    cn
    vk
    cX
    @17
    @57
    caddc
    co
    #
    cmpt
    #
    cmpt
    vn
    cn
    vk
    cX
    @17
    c1
    vn
    cv
    #
    cdiv
    co
    #
    caddc
    co
    #
    cmpt
    #
    cmpt
    vm
    cn
    @59
    @72
    vj
    vk
    cX
    @58
    @71
    @47
    @15
    wceq
    #
    @49
    @17
    @57
    caddc
    @47
    @15
    cB
    fveq2
    #
    oveq1d
    cbvmptv
    mpteq2i
    vm
    vn
    cn
    @72
    @76
    @56
    @73
    wceq
    #
    vk
    cX
    @71
    @75
    @79
    @57
    @74
    @17
    caddc
    @56
    @73
    c1
    cdiv
    oveq2
    oveq2d
    mpteq2dv
    cbvmptv
    eqtri
    vi
    vn
    cn
    @65
    vk
    cX
    @16
    @15
    @73
    @60
    cfv
    #
    cfv
    #
    cico
    co
    #
    cixp
    @61
    @73
    wceq
    #
    vk
    cX
    @64
    @82
    @83
    @63
    @81
    @16
    cico
    @83
    @15
    @62
    @80
    @61
    @73
    @60
    fveq2
    fveq1d
    oveq2d
    ixpeq2dv
    cbvmptv
    vonicclem2
    syldan
    @27
    @4
    @35
    wceq
    #
    @29
    @27
    vx
    cA
    cB
    vk
    cL
    cX
    va
    vb
    vonicc.l
    @67
    @70
    @68
    @69
    hoidmvn0val
    #
    adantr
    3eqtr4d
    @27
    @29
    wn
    #
    @17
    @16
    clt
    wbr
    #
    vk
    cX
    wrex
    #
    @5
    wph
    @86
    @88
    @26
    wph
    @86
    wa
    @28
    wn
    #
    vk
    cX
    wrex
    #
    @88
    @86
    @90
    wph
    @86
    @90
    @90
    @86
    @28
    vk
    cX
    rexnal
    bicomi
    biimpi
    adantl
    wph
    @90
    @88
    wi
    @86
    wph
    @89
    @87
    vk
    cX
    @41
    @89
    @87
    @41
    @89
    wa
    #
    @87
    @89
    @41
    @89
    simpr
    @91
    @17
    @16
    @41
    @43
    @89
    @45
    adantr
    @41
    @42
    @89
    @44
    adantr
    ltnled
    mpbird
    ex
    reximdva
    adantr
    mpd
    adantlr
    @27
    @88
    @5
    @27
    @87
    @5
    vk
    cX
    @37
    vk
    @2
    @4
    vk
    cI
    @1
    vk
    @1
    nfcv
    vk
    cI
    @22
    vonicc.i
    vk
    cX
    @18
    nfixp1
    nfcxfr
    nffv
    vk
    cA
    cB
    @3
    vk
    cA
    nfcv
    vk
    cX
    cL
    vk
    cL
    vx
    cfn
    va
    vb
    cr
    vx
    cv
    #
    cmap
    co
    #
    @93
    @92
    c0
    wceq
    #
    cc0
    @92
    @15
    va
    cv
    cfv
    @15
    vb
    cv
    cfv
    cico
    co
    cvol
    cfv
    #
    vk
    cprod
    #
    cif
    #
    cmpt2
    #
    cmpt
    vonicc.l
    vk
    vx
    cfn
    @98
    vk
    cfn
    nfcv
    va
    vb
    vk
    @93
    @93
    @97
    vk
    @93
    nfcv
    #
    @99
    @94
    vk
    cc0
    @96
    @94
    vk
    nfv
    vk
    cc0
    nfcv
    @92
    @95
    vk
    vk
    @92
    nfcv
    nfcprod1
    nfif
    nfmpt2
    nfmpt
    nfcxfr
    vk
    cX
    nfcv
    nffv
    vk
    cB
    nfcv
    nfov
    nfeq
    wph
    @38
    @87
    @5
    wi
    wi
    @26
    wph
    @38
    @87
    @5
    wph
    @38
    @87
    w3a
    #
    c0
    @1
    cfv
    #
    cc0
    @2
    @4
    wph
    @38
    @101
    cc0
    wceq
    @87
    wph
    @1
    wph
    cX
    vonicc.x
    vonmea
    mea0
    3ad2ant1
    @100
    cI
    c0
    @1
    @100
    cI
    @22
    c0
    @23
    @100
    vonicc.i
    a1i
    @100
    @18
    c0
    wceq
    #
    vk
    cX
    wrex
    #
    @22
    c0
    wceq
    @100
    @38
    @102
    @103
    wph
    @38
    @87
    simp2
    @100
    @102
    @87
    wph
    @38
    @87
    simp3
    wph
    @38
    @102
    @87
    wb
    #
    @87
    @41
    @16
    cxr
    wcel
    @17
    cxr
    wcel
    @104
    @41
    cr
    cxr
    @16
    ressxr
    @44
    sseldi
    @41
    cr
    cxr
    @17
    ressxr
    @45
    sseldi
    @16
    @17
    icc0
    syl2anc
    3adant3
    mpbird
    @102
    vk
    cX
    rspe
    syl2anc
    vk
    cX
    @18
    ixp0
    syl
    eqtrd
    fveq2d
    @100
    @4
    @35
    cc0
    wph
    @38
    @84
    @87
    wph
    @38
    @26
    @84
    @38
    @26
    wph
    cX
    @15
    ne0i
    adantl
    @85
    syldan
    3adant3
    wph
    @47
    cX
    wcel
    #
    @49
    @48
    clt
    wbr
    #
    w3a
    #
    @35
    cc0
    wceq
    #
    wi
    @100
    @108
    wi
    vj
    vk
    @77
    @107
    @100
    @108
    @77
    @105
    @38
    @106
    @87
    wph
    @47
    @15
    cX
    eleq1
    @77
    @49
    @17
    @48
    @16
    clt
    @78
    @47
    @15
    cA
    fveq2
    breq12d
    3anbi23d
    imbi1d
    @107
    cX
    @34
    @47
    vk
    @107
    vk
    nfv
    wph
    @105
    @66
    @106
    vonicc.x
    3ad2ant1
    wph
    @105
    @38
    @34
    cc
    wcel
    @106
    @41
    @34
    @41
    @42
    @43
    @34
    cr
    wcel
    @44
    @45
    @16
    @17
    volicore
    syl2anc
    recnd
    3ad2antl1
    wph
    @105
    @106
    simp2
    @107
    @52
    wa
    @34
    @48
    @49
    cico
    co
    #
    cvol
    cfv
    #
    cc0
    @52
    @34
    @110
    wceq
    @107
    @52
    @33
    @109
    cvol
    @52
    @16
    @48
    @17
    @49
    cico
    @53
    @54
    oveq12d
    fveq2d
    adantl
    @107
    @110
    cc0
    wceq
    @52
    @107
    @110
    @50
    @49
    @48
    cmin
    co
    #
    cc0
    cif
    #
    cc0
    wph
    @105
    @110
    @112
    wceq
    #
    @106
    wph
    @105
    wa
    #
    @48
    cr
    wcel
    @49
    cr
    wcel
    @113
    wph
    cX
    cr
    @47
    cA
    vonicc.a
    ffvelrnda
    #
    wph
    cX
    cr
    @47
    cB
    vonicc.b
    ffvelrnda
    #
    @48
    @49
    volico2
    syl2anc
    3adant3
    @107
    @50
    @111
    cc0
    @107
    @106
    @50
    wn
    #
    wph
    @105
    @106
    simp3
    wph
    @105
    @106
    @117
    wb
    @106
    @114
    @49
    @48
    @116
    @115
    ltnled
    3adant3
    mpbid
    iffalsed
    eqtrd
    adantr
    eqtrd
    fprodeq0g
    chvarv
    eqtrd
    3eqtr4d
    3exp
    adantr
    rexlimd
    imp
    syldan
    pm2.61dan
    syldan
    pm2.61dan
end
