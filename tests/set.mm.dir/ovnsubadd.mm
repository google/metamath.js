include "c0.mm"
include "wceq.mm"
include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "covoln.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cc0.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "adantl.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "wss.mm"
include "wral.mm"
include "wcel.mm"
include "cpw.mm"
include "wf.mm"
include "adantr.mm"
include "simpr.mm"
include "ffvelrnd.mm"
include "elpwi.mm"
include "syl.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "oveq2.mm"
include "sseqtrd.mm"
include "ovn0val.mm"
include "eqtrd.mm"
include "cvv.mm"
include "nnex.mm"
include "a1i.mm"
include "cpnf.mm"
include "cicc.mm"
include "cfn.mm"
include "ovncl.mm"
include "eqid.mm"
include "fmptd.mm"
include "sge0ge0.mm"
include "eqbrtrd.mm"
include "wn.mm"
include "cxr.mm"
include "ovnxrcl.mm"
include "sge0xrcl.mm"
include "crp.mm"
include "cico.mm"
include "ccom.mm"
include "cixp.mm"
include "cxp.mm"
include "crab.mm"
include "cvol.mm"
include "cprod.mm"
include "cxad.mm"
include "wrex.mm"
include "ad2antrr.mm"
include "wne.mm"
include "neqne.mm"
include "ad2antlr.mm"
include "sseq1.mm"
include "rabbidv.mm"
include "cbvmptv.mm"
include "coeq2d.mm"
include "ixpeq2dv.mm"
include "cbvixpv.mm"
include "syl6eq.mm"
include "cbviunv.mm"
include "sseq2i.mm"
include "rabbii.mm"
include "mpteq2i.mm"
include "fveq1i.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "fveq2d.mm"
include "cbvprodv.mm"
include "fveq12d.mm"
include "fveq2i.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "anbi12d.mm"
include "rabbidva2.mm"
include "fveq1.mm"
include "mpteq2dv.mm"
include "breq1d.mm"
include "cbvrabv.mm"
include "breq2d.mm"
include "ovnsubaddlem2.mm"
include "xrlexaddrp.mm"
include "pm2.61dan.mm"

theorem ovnsubadd
  let wph: wff ph
  let cA: class A
  let vn: setvar n
  let cX: class X
  let va: setvar a
  let ve: setvar e
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  let vy: setvar y
  let vz: setvar z
  let vb: setvar b
  let vd: setvar d
  let vf: setvar f
  let vm: setvar m
  let vh: setvar h
  let vo: setvar o
  let vx: setvar x
  assume ovnsubadd.1: |- ( ph -> X e. Fin )
  assume ovnsubadd.2: |- ( ph -> A : NN --> ~P ( RR ^m X ) )

  disjoint A n
  disjoint X n
  disjoint n ph
  disjoint A a
  disjoint A e
  disjoint A i
  disjoint A j
  disjoint A k
  disjoint A l
  disjoint a e
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a l
  disjoint a n
  disjoint e i
  disjoint e j
  disjoint e k
  disjoint e l
  disjoint e n
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i n
  disjoint j k
  disjoint j l
  disjoint j n
  disjoint k l
  disjoint k n
  disjoint l n
  disjoint A y
  disjoint a y
  disjoint e y
  disjoint i y
  disjoint j y
  disjoint k y
  disjoint n y
  disjoint A z
  disjoint a z
  disjoint i z
  disjoint j z
  disjoint k z
  disjoint n z
  disjoint X a
  disjoint X b
  disjoint X d
  disjoint X e
  disjoint X f
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X l
  disjoint X m
  disjoint a b
  disjoint a d
  disjoint a f
  disjoint a m
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint b l
  disjoint b m
  disjoint b n
  disjoint d e
  disjoint d f
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d l
  disjoint d m
  disjoint d n
  disjoint e f
  disjoint e m
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f l
  disjoint f m
  disjoint f n
  disjoint i m
  disjoint j m
  disjoint k m
  disjoint l m
  disjoint m n
  disjoint X h
  disjoint a h
  disjoint d h
  disjoint e h
  disjoint f h
  disjoint h i
  disjoint h j
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint X o
  disjoint a o
  disjoint d o
  disjoint e o
  disjoint h o
  disjoint i o
  disjoint j o
  disjoint k o
  disjoint m o
  disjoint n o
  disjoint X y
  disjoint X z
  disjoint a ph
  disjoint e ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint ph y
  disjoint l o
  disjoint k x
  assert |- ( ph -> ( ( voln* ` X ) ` U_ n e. NN ( A ` n ) ) <_ ( sum^ ` ( n e. NN |-> ( ( voln* ` X ) ` ( A ` n ) ) ) ) )

  proof
    wph
    cX
    c0
    wceq
    #
    vn
    cn
    vn
    cv
    #
    cA
    cfv
    #
    ciun
    #
    cX
    covoln
    cfv
    #
    cfv
    #
    vn
    cn
    @2
    @4
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    cle
    wbr
    wph
    @0
    wa
    #
    @5
    cc0
    @8
    cle
    @9
    @5
    @3
    c0
    covoln
    cfv
    #
    cfv
    #
    cc0
    @0
    @5
    @11
    wceq
    wph
    @0
    @3
    @4
    @10
    cX
    c0
    covoln
    fveq2
    fveq1d
    adantl
    @9
    @3
    @9
    @3
    cr
    cX
    cmap
    co
    #
    cr
    c0
    cmap
    co
    #
    wph
    @3
    @12
    wss
    #
    @0
    wph
    @2
    @12
    wss
    #
    vn
    cn
    wral
    @14
    wph
    @15
    vn
    cn
    wph
    @1
    cn
    wcel
    #
    wa
    #
    @2
    @12
    cpw
    #
    wcel
    @15
    @17
    cn
    @18
    @1
    cA
    wph
    cn
    @18
    cA
    wf
    #
    @16
    ovnsubadd.2
    adantr
    wph
    @16
    simpr
    ffvelrnd
    @2
    @12
    elpwi
    syl
    #
    ralrimiva
    vn
    cn
    @2
    @12
    iunss
    sylibr
    #
    adantr
    @0
    @12
    @13
    wceq
    wph
    cX
    c0
    cr
    cmap
    oveq2
    adantl
    sseqtrd
    ovn0val
    eqtrd
    wph
    cc0
    @8
    cle
    wbr
    @0
    wph
    @7
    cvv
    cn
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    #
    wph
    vn
    cn
    @6
    cc0
    cpnf
    cicc
    co
    @7
    @17
    @2
    cX
    wph
    cX
    cfn
    wcel
    #
    @16
    ovnsubadd.1
    adantr
    @20
    ovncl
    @7
    eqid
    fmptd
    #
    sge0ge0
    adantr
    eqbrtrd
    wph
    @0
    wn
    #
    wa
    #
    vy
    @5
    @8
    wph
    @5
    cxr
    wcel
    @25
    wph
    @3
    cX
    ovnsubadd.1
    @21
    ovnxrcl
    adantr
    wph
    @8
    cxr
    wcel
    @25
    wph
    @7
    cvv
    cn
    @22
    @24
    sge0xrcl
    adantr
    @26
    vy
    cv
    #
    crp
    wcel
    #
    wa
    vz
    cA
    vb
    @18
    vb
    cv
    #
    vj
    cn
    vk
    cX
    vk
    cv
    #
    cico
    vj
    cv
    #
    vl
    cv
    #
    cfv
    #
    ccom
    #
    cfv
    #
    cixp
    #
    ciun
    #
    wss
    #
    vl
    cr
    cr
    cxp
    cX
    cmap
    co
    #
    cn
    cmap
    co
    #
    crab
    #
    cmpt
    #
    vd
    @18
    vf
    crp
    vo
    cn
    vo
    cv
    #
    vm
    cv
    #
    cfv
    #
    vh
    @39
    cX
    vd
    cv
    #
    cico
    vh
    cv
    ccom
    #
    cfv
    #
    cvol
    cfv
    #
    vd
    cprod
    #
    cmpt
    #
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    @46
    @4
    cfv
    #
    vf
    cv
    #
    cxad
    co
    #
    cle
    wbr
    #
    vm
    @46
    vb
    @18
    @29
    vo
    cn
    vd
    cX
    @46
    cico
    @43
    @32
    cfv
    #
    ccom
    #
    cfv
    #
    cixp
    #
    ciun
    #
    wss
    #
    vl
    @40
    crab
    #
    cmpt
    #
    cfv
    #
    crab
    #
    cmpt
    #
    cmpt
    ve
    vh
    vi
    vj
    vk
    vn
    @27
    vh
    @39
    cX
    @30
    @47
    cfv
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    cmpt
    #
    cX
    va
    @18
    va
    cv
    #
    vj
    cn
    vk
    cX
    @30
    cico
    @31
    vi
    cv
    #
    cfv
    #
    ccom
    cfv
    #
    cixp
    ciun
    wss
    vz
    cv
    vj
    cn
    cX
    @77
    cvol
    cfv
    vk
    cprod
    cmpt
    csumge0
    cfv
    wceq
    wa
    vi
    @40
    wrex
    vz
    cxr
    crab
    cmpt
    #
    va
    vl
    wph
    @23
    @25
    @28
    ovnsubadd.1
    ad2antrr
    @25
    cX
    c0
    wne
    wph
    @28
    cX
    c0
    neqne
    ad2antlr
    wph
    @19
    @25
    @28
    ovnsubadd.2
    ad2antrr
    @26
    @28
    simpr
    @78
    eqid
    vb
    va
    @18
    @41
    @74
    @37
    wss
    #
    vl
    @40
    crab
    @29
    @74
    wceq
    @38
    @79
    vl
    @40
    @29
    @74
    @37
    sseq1
    rabbidv
    cbvmptv
    @73
    eqid
    vd
    va
    @18
    @69
    ve
    crp
    vj
    cn
    @76
    @73
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    @74
    @4
    cfv
    #
    ve
    cv
    #
    cxad
    co
    #
    cle
    wbr
    #
    vi
    @74
    @42
    cfv
    #
    crab
    #
    cmpt
    #
    @46
    @74
    wceq
    #
    @69
    vf
    crp
    @82
    @83
    @56
    cxad
    co
    #
    cle
    wbr
    #
    vi
    @87
    crab
    #
    cmpt
    @89
    @90
    vf
    crp
    @68
    @93
    @90
    @68
    vj
    cn
    @31
    @44
    cfv
    #
    @73
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    @91
    cle
    wbr
    #
    vm
    @87
    crab
    @93
    @90
    @58
    @98
    vm
    @67
    @87
    @90
    @44
    @67
    wcel
    @44
    @87
    wcel
    @58
    @98
    @90
    @67
    @87
    @44
    @90
    @67
    @46
    @42
    cfv
    @87
    @46
    @66
    @42
    vb
    @18
    @65
    @41
    @64
    @38
    vl
    @40
    @63
    @37
    @29
    vo
    vj
    cn
    @62
    @36
    @43
    @31
    wceq
    #
    @62
    vd
    cX
    @46
    @34
    cfv
    #
    cixp
    @36
    @99
    vd
    cX
    @61
    @100
    @99
    @46
    @60
    @34
    @99
    @59
    @33
    cico
    @43
    @31
    @32
    fveq2
    coeq2d
    fveq1d
    ixpeq2dv
    vd
    vk
    cX
    @100
    @35
    @46
    @30
    @34
    fveq2
    cbvixpv
    syl6eq
    cbviunv
    sseq2i
    rabbii
    mpteq2i
    fveq1i
    @46
    @74
    @42
    fveq2
    syl5eq
    eleq2d
    @90
    @54
    @97
    @57
    @91
    cle
    @54
    @97
    wceq
    @90
    @53
    @96
    csumge0
    vo
    vj
    cn
    @52
    @95
    @99
    @45
    @94
    @51
    @73
    @51
    @73
    wceq
    @99
    vh
    @39
    @50
    @72
    cX
    @49
    @71
    vd
    vk
    @46
    @30
    wceq
    @48
    @70
    cvol
    @46
    @30
    @47
    fveq2
    fveq2d
    cbvprodv
    mpteq2i
    a1i
    @43
    @31
    @44
    fveq2
    fveq12d
    cbvmptv
    fveq2i
    a1i
    @90
    @55
    @83
    @56
    cxad
    @46
    @74
    @4
    fveq2
    oveq1d
    breq12d
    anbi12d
    rabbidva2
    @98
    @92
    vm
    vi
    @87
    @44
    @75
    wceq
    #
    @97
    @82
    @91
    cle
    @101
    @96
    @81
    csumge0
    @101
    vj
    cn
    @95
    @80
    @101
    @94
    @76
    @73
    @31
    @44
    @75
    fveq1
    fveq2d
    mpteq2dv
    fveq2d
    breq1d
    cbvrabv
    syl6eq
    mpteq2dv
    vf
    ve
    crp
    @93
    @88
    @56
    @84
    wceq
    #
    @92
    @86
    vi
    @87
    @102
    @91
    @85
    @82
    cle
    @56
    @84
    @83
    cxad
    oveq2
    breq2d
    rabbidv
    cbvmptv
    syl6eq
    cbvmptv
    ovnsubaddlem2
    xrlexaddrp
    pm2.61dan
end
