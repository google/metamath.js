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
include "cioo.mm"
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
include "cxr.mm"
include "wss.mm"
include "ressxr.mm"
include "fssd.mm"
include "ioovonmbl.mm"
include "von0val.mm"
include "oveqd.mm"
include "3eqtr4d.mm"
include "wn.mm"
include "wne.mm"
include "neqne.mm"
include "clt.mm"
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
include "volico.mm"
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
include "oveq2.mm"
include "oveq2d.mm"
include "mpteq2dv.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nffv.mm"
include "nfov.mm"
include "nfixp.mm"
include "fveq1d.mm"
include "ixpeq2dv.mm"
include "cbvmpt.mm"
include "vonioolem2.mm"
include "syldan.mm"
include "hoidmvn0val.mm"
include "cle.mm"
include "wrex.mm"
include "rexnal.mm"
include "bicomi.mm"
include "wi.mm"
include "lenltd.mm"
include "mpbird.mm"
include "reximdva.mm"
include "mpd.mm"
include "adantlr.mm"
include "nfixp1.mm"
include "nfcxfr.mm"
include "nfeq.mm"
include "w3a.mm"
include "vonmea.mm"
include "mea0.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "sseldi.mm"
include "3adant3.mm"
include "ioo0.mm"
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

theorem vonioo
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
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  assume vonioo.x: |- ( ph -> X e. Fin )
  assume vonioo.a: |- ( ph -> A : X --> RR )
  assume vonioo.b: |- ( ph -> B : X --> RR )
  assume vonioo.i: |- I = X_ k e. X ( ( A ` k ) (,) ( B ` k ) )
  assume vonioo.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )

  disjoint A a
  disjoint A b
  disjoint A k
  disjoint a b
  disjoint a k
  disjoint b k
  disjoint B a
  disjoint B b
  disjoint B k
  disjoint L k
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
  disjoint A j
  disjoint A m
  disjoint A n
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint B j
  disjoint B m
  disjoint B n
  disjoint I n
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
    vonioo.l
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
    vonioo.a
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
    vonioo.b
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
    cioo
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
    vonioo.i
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
    @6
    c0
    cr
    cxr
    cA
    @11
    cr
    cxr
    wss
    @6
    ressxr
    a1i
    #
    fssd
    @6
    c0
    cr
    cxr
    cB
    @14
    @25
    fssd
    ioovonmbl
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
    @26
    @27
    wph
    cX
    c0
    neqne
    adantl
    wph
    @27
    wa
    #
    @16
    @17
    clt
    wbr
    #
    vk
    cX
    wral
    #
    @5
    @28
    @30
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
    @31
    @36
    @33
    @31
    cX
    @35
    @32
    vk
    @31
    @35
    @32
    wceq
    #
    vk
    cX
    @28
    @30
    vk
    @28
    vk
    nfv
    #
    @29
    vk
    cX
    nfra1
    nfan
    @31
    @15
    cX
    wcel
    #
    @37
    @31
    @39
    wa
    @35
    @29
    @32
    cc0
    cif
    #
    @32
    wph
    @39
    @35
    @40
    wceq
    #
    @27
    @30
    wph
    @39
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
    @41
    wph
    cX
    cr
    @15
    cA
    vonioo.a
    ffvelrnda
    #
    wph
    cX
    cr
    @15
    cB
    vonioo.b
    ffvelrnda
    #
    @16
    @17
    volico
    syl2anc
    ad4ant14
    @30
    @39
    @40
    @32
    wceq
    @28
    @30
    @39
    wa
    @29
    @32
    cc0
    @29
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
    @28
    @30
    vj
    cv
    #
    cA
    cfv
    #
    @48
    cB
    cfv
    #
    clt
    wbr
    #
    vj
    cX
    wral
    #
    @2
    @33
    wceq
    @30
    @52
    @28
    @30
    @52
    @29
    @51
    vk
    vj
    cX
    @15
    @48
    wceq
    #
    @16
    @49
    @17
    @50
    clt
    @15
    @48
    cA
    fveq2
    #
    @15
    @48
    cB
    fveq2
    #
    breq12d
    cbvralv
    #
    biimpi
    adantl
    @28
    @52
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
    vm
    cn
    vk
    cX
    @15
    @57
    @61
    cfv
    #
    cfv
    #
    @17
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
    @28
    cX
    cfn
    wcel
    #
    @52
    wph
    @66
    @27
    vonioo.x
    adantr
    #
    adantr
    @28
    @9
    @52
    wph
    @9
    @27
    vonioo.a
    adantr
    #
    adantr
    @28
    @12
    @52
    wph
    @12
    @27
    vonioo.b
    adantr
    #
    adantr
    @28
    @27
    @52
    wph
    @27
    simpr
    #
    adantr
    @52
    @39
    @29
    @28
    @52
    @30
    @39
    @29
    @56
    @47
    sylanbr
    adantll
    vonioo.i
    vm
    vn
    cn
    @60
    vk
    cX
    @16
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
    @57
    @71
    wceq
    #
    @60
    vk
    cX
    @16
    @58
    caddc
    co
    #
    cmpt
    #
    @74
    @60
    @77
    wceq
    @75
    vj
    vk
    cX
    @59
    @76
    @48
    @15
    wceq
    #
    @49
    @16
    @58
    caddc
    @48
    @15
    cA
    fveq2
    #
    oveq1d
    cbvmptv
    a1i
    @75
    vk
    cX
    @76
    @73
    @75
    @58
    @72
    @16
    caddc
    @57
    @71
    c1
    cdiv
    oveq2
    oveq2d
    mpteq2dv
    eqtrd
    cbvmptv
    vm
    vn
    cn
    @65
    vk
    cX
    @15
    @71
    @61
    cfv
    #
    cfv
    #
    @17
    cico
    co
    #
    cixp
    vn
    @65
    nfcv
    vk
    vm
    cX
    @82
    vm
    cX
    nfcv
    vm
    @81
    @17
    cico
    vm
    @15
    @80
    vm
    cn
    @60
    @71
    nffvmpt1
    vm
    @15
    nfcv
    nffv
    vm
    cico
    nfcv
    vm
    @17
    nfcv
    nfov
    nfixp
    @75
    vk
    cX
    @64
    @82
    @75
    @63
    @81
    @17
    cico
    @75
    @15
    @62
    @80
    @57
    @71
    @61
    fveq2
    fveq1d
    oveq1d
    ixpeq2dv
    cbvmpt
    vonioolem2
    syldan
    @28
    @4
    @36
    wceq
    #
    @30
    @28
    vx
    cA
    cB
    vk
    cL
    cX
    va
    vb
    vonioo.l
    @67
    @70
    @68
    @69
    hoidmvn0val
    #
    adantr
    3eqtr4d
    @28
    @30
    wn
    #
    @17
    @16
    cle
    wbr
    #
    vk
    cX
    wrex
    #
    @5
    wph
    @85
    @87
    @27
    wph
    @85
    wa
    @29
    wn
    #
    vk
    cX
    wrex
    #
    @87
    @85
    @89
    wph
    @85
    @89
    @89
    @85
    @29
    vk
    cX
    rexnal
    bicomi
    biimpi
    adantl
    wph
    @89
    @87
    wi
    @85
    wph
    @88
    @86
    vk
    cX
    @42
    @88
    @86
    @42
    @88
    wa
    #
    @86
    @88
    @42
    @88
    simpr
    @90
    @17
    @16
    @42
    @44
    @88
    @46
    adantr
    @42
    @43
    @88
    @45
    adantr
    lenltd
    mpbird
    ex
    reximdva
    adantr
    mpd
    adantlr
    @28
    @87
    @5
    @28
    @86
    @5
    vk
    cX
    @38
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
    vonioo.i
    vk
    cX
    @18
    nfixp1
    nfcxfr
    nffv
    vk
    @4
    nfcv
    nfeq
    wph
    @39
    @86
    @5
    wi
    wi
    @27
    wph
    @39
    @86
    @5
    wph
    @39
    @86
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
    @39
    @92
    cc0
    wceq
    @86
    wph
    @1
    wph
    cX
    vonioo.x
    vonmea
    mea0
    3ad2ant1
    @91
    cI
    c0
    @1
    @91
    cI
    @22
    c0
    @23
    @91
    vonioo.i
    a1i
    @91
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
    @91
    @39
    @93
    @94
    wph
    @39
    @86
    simp2
    @91
    @93
    @86
    wph
    @39
    @86
    simp3
    @91
    @16
    cxr
    wcel
    #
    @17
    cxr
    wcel
    #
    @93
    @86
    wb
    wph
    @39
    @95
    @86
    @42
    cr
    cxr
    @16
    ressxr
    @45
    sseldi
    3adant3
    wph
    @39
    @96
    @86
    @42
    cr
    cxr
    @17
    ressxr
    @46
    sseldi
    3adant3
    @16
    @17
    ioo0
    syl2anc
    mpbird
    @93
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
    @91
    @4
    @36
    cc0
    wph
    @39
    @83
    @86
    wph
    @39
    @27
    @83
    @39
    @27
    wph
    cX
    @15
    ne0i
    adantl
    @84
    syldan
    3adant3
    wph
    @48
    cX
    wcel
    #
    @50
    @49
    cle
    wbr
    #
    w3a
    #
    @36
    cc0
    wceq
    #
    wi
    @91
    @100
    wi
    vj
    vk
    @78
    @99
    @91
    @100
    @78
    @97
    @39
    @98
    @86
    wph
    @48
    @15
    cX
    eleq1
    @78
    @50
    @17
    @49
    @16
    cle
    @48
    @15
    cB
    fveq2
    @79
    breq12d
    3anbi23d
    imbi1d
    @99
    cX
    @35
    @48
    vk
    @99
    vk
    nfv
    wph
    @97
    @66
    @98
    vonioo.x
    3ad2ant1
    wph
    @97
    @39
    @35
    cc
    wcel
    @98
    @42
    @35
    @42
    @43
    @44
    @35
    cr
    wcel
    @45
    @46
    @16
    @17
    volicore
    syl2anc
    recnd
    3ad2antl1
    wph
    @97
    @98
    simp2
    @99
    @53
    wa
    @35
    @49
    @50
    cico
    co
    #
    cvol
    cfv
    #
    cc0
    @53
    @35
    @102
    wceq
    @99
    @53
    @34
    @101
    cvol
    @53
    @16
    @49
    @17
    @50
    cico
    @54
    @55
    oveq12d
    fveq2d
    adantl
    @99
    @102
    cc0
    wceq
    @53
    @99
    @102
    @51
    @50
    @49
    cmin
    co
    #
    cc0
    cif
    #
    cc0
    wph
    @97
    @102
    @104
    wceq
    #
    @98
    wph
    @97
    wa
    #
    @49
    cr
    wcel
    @50
    cr
    wcel
    @105
    wph
    cX
    cr
    @48
    cA
    vonioo.a
    ffvelrnda
    #
    wph
    cX
    cr
    @48
    cB
    vonioo.b
    ffvelrnda
    #
    @49
    @50
    volico
    syl2anc
    3adant3
    @99
    @51
    @103
    cc0
    @99
    @98
    @51
    wn
    #
    wph
    @97
    @98
    simp3
    wph
    @97
    @98
    @109
    wb
    @98
    @106
    @50
    @49
    @108
    @107
    lenltd
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
