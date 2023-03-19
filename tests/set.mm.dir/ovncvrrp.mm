include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "cn.mm"
include "cmpt.mm"
include "csumge0.mm"
include "covoln.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "cico.mm"
include "ccom.mm"
include "cixp.mm"
include "ciun.mm"
include "wss.mm"
include "cvol.mm"
include "cprod.mm"
include "wceq.mm"
include "cr.mm"
include "cxp.mm"
include "cmap.mm"
include "wrex.mm"
include "cxr.mm"
include "crab.mm"
include "eqid.mm"
include "ovnlerp.mm"
include "w3a.mm"
include "simp1.mm"
include "simp3.mm"
include "rabid.mm"
include "biimpi.mm"
include "simprd.mm"
include "adantr.mm"
include "3adant1.mm"
include "nfv.mm"
include "nfe1.mm"
include "simp1l.mm"
include "simp2.mm"
include "simp3l.mm"
include "id.mm"
include "fveq1.mm"
include "coeq2d.mm"
include "fveq1d.mm"
include "ixpeq2dv.mm"
include "iuneq2d.mm"
include "sseq2d.mm"
include "elrab.mm"
include "sylibr.mm"
include "cpw.mm"
include "cvv.mm"
include "a1i.mm"
include "sseq1.mm"
include "rabbidv.mm"
include "adantl.mm"
include "wb.mm"
include "ovexd.mm"
include "ssexd.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmptd.mm"
include "eqcomd.mm"
include "3ad2ant1.mm"
include "eleqtrd.mm"
include "syl3anc.mm"
include "coeq2.mm"
include "fveq2d.mm"
include "prodeq2ad.mm"
include "wf.mm"
include "elmapi.mm"
include "simpr.mm"
include "ffvelrnd.mm"
include "prodex.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "eqbrtrd.mm"
include "3adant1l.mm"
include "3adant3l.mm"
include "jca.mm"
include "19.8a.mm"
include "3exp.mm"
include "rexlimd.mm"
include "imp.mm"
include "syl21anc.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "bicomi.mm"
include "crp.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfrab.mm"
include "nfmpt.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "rabbidva2.mm"
include "mpteq2dv.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "rpex.mm"
include "mptex.mm"
include "oveq2.mm"
include "fvex.mm"
include "ex.mm"
include "eximdv.mm"

theorem ovncvrrp
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cD: class D
  let ve: setvar e
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cE: class E
  let cL: class L
  let cX: class X
  let va: setvar a
  let vl: setvar l
  let vb: setvar b
  let vz: setvar z
  let vx: setvar x
  assume ovncvrrp.x: |- ( ph -> X e. Fin )
  assume ovncvrrp.n0: |- ( ph -> X =/= (/) )
  assume ovncvrrp.a: |- ( ph -> A C_ ( RR ^m X ) )
  assume ovncvrrp.e: |- ( ph -> E e. RR+ )
  assume ovncvrrp.c: |- C = ( a e. ~P ( RR ^m X ) |-> { l e. ( ( ( RR X. RR ) ^m X ) ^m NN ) | a C_ U_ j e. NN X_ k e. X ( ( [,) o. ( l ` j ) ) ` k ) } )
  assume ovncvrrp.l: |- L = ( h e. ( ( RR X. RR ) ^m X ) |-> prod_ k e. X ( vol ` ( ( [,) o. h ) ` k ) ) )
  assume ovncvrrp.d: |- D = ( a e. ~P ( RR ^m X ) |-> ( e e. RR+ |-> { i e. ( C ` a ) | ( sum^ ` ( j e. NN |-> ( L ` ( i ` j ) ) ) ) <_ ( ( ( voln* ` X ) ` a ) +e e ) } ) )

  disjoint A a
  disjoint A e
  disjoint A i
  disjoint a e
  disjoint a i
  disjoint e i
  disjoint A l
  disjoint a l
  disjoint i l
  disjoint C e
  disjoint C i
  disjoint E e
  disjoint E i
  disjoint L a
  disjoint L e
  disjoint X a
  disjoint X e
  disjoint X i
  disjoint X j
  disjoint a j
  disjoint e j
  disjoint i j
  disjoint X h
  disjoint X k
  disjoint h i
  disjoint h j
  disjoint h k
  disjoint i k
  disjoint j k
  disjoint X l
  disjoint a k
  disjoint j l
  disjoint k l
  disjoint a ph
  disjoint e ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint A b
  disjoint a b
  disjoint b e
  disjoint b i
  disjoint A z
  disjoint i z
  disjoint C b
  disjoint C z
  disjoint E b
  disjoint E z
  disjoint L b
  disjoint L z
  disjoint X b
  disjoint b j
  disjoint X z
  disjoint j z
  disjoint k z
  disjoint b ph
  disjoint ph z
  disjoint k x
  assert |- ( ph -> E. i i e. ( ( D ` A ) ` E ) )

  proof
    wph
    vi
    cv
    #
    cA
    cC
    cfv
    #
    wcel
    #
    vj
    cn
    vj
    cv
    #
    @0
    cfv
    #
    cL
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    cA
    cX
    covoln
    cfv
    #
    cfv
    #
    cE
    cxad
    co
    #
    cle
    wbr
    #
    wa
    #
    vi
    wex
    #
    @0
    cE
    cA
    cD
    cfv
    #
    cfv
    #
    wcel
    #
    vi
    wex
    wph
    vz
    cv
    #
    @10
    cle
    wbr
    #
    vz
    cA
    vj
    cn
    vk
    cX
    vk
    cv
    #
    cico
    @4
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
    @17
    vj
    cn
    cX
    @21
    cvol
    cfv
    #
    vk
    cprod
    #
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vi
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
    wrex
    #
    vz
    cxr
    crab
    #
    wrex
    @13
    wph
    vz
    cA
    vi
    vj
    vk
    cE
    @34
    cX
    ovncvrrp.x
    ovncvrrp.n0
    ovncvrrp.a
    ovncvrrp.e
    @34
    eqid
    ovnlerp
    wph
    @18
    @13
    vz
    @34
    wph
    @17
    @34
    wcel
    #
    @18
    @13
    wph
    @35
    @18
    w3a
    wph
    @18
    @33
    @13
    wph
    @35
    @18
    simp1
    wph
    @35
    @18
    simp3
    @35
    @18
    @33
    wph
    @35
    @33
    @18
    @35
    @17
    cxr
    wcel
    #
    @33
    @35
    @36
    @33
    wa
    @33
    vz
    cxr
    rabid
    biimpi
    simprd
    adantr
    3adant1
    wph
    @18
    wa
    #
    @33
    @13
    @37
    @30
    @13
    vi
    @32
    @37
    vi
    nfv
    @12
    vi
    nfe1
    @37
    @0
    @32
    wcel
    #
    @30
    @13
    @37
    @38
    @30
    w3a
    #
    @12
    @13
    @39
    @2
    @11
    @39
    wph
    @38
    @24
    @2
    wph
    @18
    @38
    @30
    simp1l
    @37
    @38
    @30
    simp2
    @37
    @38
    @24
    @29
    simp3l
    wph
    @38
    @24
    w3a
    @0
    cA
    vj
    cn
    vk
    cX
    @19
    cico
    @3
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
    @32
    crab
    #
    @1
    @38
    @24
    @0
    @47
    wcel
    #
    wph
    @38
    @24
    wa
    #
    @49
    @48
    @49
    id
    @46
    @24
    vl
    @0
    @32
    @40
    @0
    wceq
    #
    @45
    @23
    cA
    @50
    vj
    cn
    @44
    @22
    @50
    vk
    cX
    @43
    @21
    @50
    @19
    @42
    @20
    @50
    @41
    @4
    cico
    @3
    @40
    @0
    fveq1
    coeq2d
    fveq1d
    ixpeq2dv
    iuneq2d
    sseq2d
    elrab
    sylibr
    3adant1
    wph
    @38
    @47
    @1
    wceq
    @24
    wph
    @1
    @47
    wph
    va
    cA
    va
    cv
    #
    @45
    wss
    #
    vl
    @32
    crab
    #
    @47
    cr
    cX
    cmap
    co
    #
    cpw
    #
    cC
    cvv
    cC
    va
    @55
    @53
    cmpt
    #
    wceq
    wph
    ovncvrrp.c
    a1i
    @51
    cA
    wceq
    #
    @53
    @47
    wceq
    wph
    @57
    @52
    @46
    vl
    @32
    @51
    cA
    @45
    sseq1
    rabbidv
    adantl
    wph
    cA
    @55
    wcel
    #
    cA
    @54
    wss
    #
    ovncvrrp.a
    wph
    cA
    cvv
    wcel
    @58
    @59
    wb
    wph
    cA
    @54
    cvv
    wph
    cr
    cX
    cmap
    ovexd
    ovncvrrp.a
    ssexd
    cA
    @54
    cvv
    elpwg
    syl
    mpbird
    #
    @47
    cvv
    wcel
    wph
    @46
    vl
    @32
    @31
    cn
    cmap
    ovex
    rabex
    a1i
    fvmptd
    eqcomd
    3ad2ant1
    eleqtrd
    syl3anc
    @37
    @38
    @29
    @11
    @24
    @18
    @38
    @29
    @11
    wph
    @18
    @38
    @29
    w3a
    @7
    @17
    @10
    cle
    @38
    @29
    @7
    @17
    wceq
    @18
    @38
    @29
    wa
    @7
    @28
    @17
    @38
    @7
    @28
    wceq
    @29
    @38
    @6
    @27
    csumge0
    @38
    vj
    cn
    @5
    @26
    @38
    @3
    cn
    wcel
    #
    wa
    #
    vh
    @4
    cX
    @19
    cico
    vh
    cv
    #
    ccom
    #
    cfv
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    @26
    @31
    cL
    cvv
    cL
    vh
    @31
    @67
    cmpt
    wceq
    @62
    ovncvrrp.l
    a1i
    @63
    @4
    wceq
    #
    @67
    @26
    wceq
    @62
    @68
    cX
    @66
    @25
    vk
    @68
    @65
    @21
    cvol
    @68
    @19
    @64
    @20
    @63
    @4
    cico
    coeq2
    fveq1d
    fveq2d
    prodeq2ad
    adantl
    @62
    cn
    @31
    @3
    @0
    @38
    cn
    @31
    @0
    wf
    @61
    @0
    @31
    cn
    elmapi
    adantr
    @38
    @61
    simpr
    ffvelrnd
    @26
    cvv
    wcel
    @62
    cX
    @25
    vk
    prodex
    a1i
    fvmptd
    mpteq2dva
    fveq2d
    adantr
    @29
    @28
    @17
    wceq
    @38
    @29
    @17
    @28
    @29
    id
    eqcomd
    adantl
    eqtrd
    3adant1
    @18
    @38
    @29
    simp1
    eqbrtrd
    3adant1l
    3adant3l
    jca
    @12
    vi
    19.8a
    syl
    3exp
    rexlimd
    imp
    syl21anc
    3exp
    rexlimdv
    mpd
    wph
    @12
    @16
    vi
    wph
    @12
    @16
    wph
    @12
    wa
    #
    @0
    @11
    vi
    @1
    crab
    #
    @15
    @12
    @0
    @70
    wcel
    #
    wph
    @12
    @71
    @71
    @12
    @11
    vi
    @1
    rabid
    bicomi
    biimpi
    adantl
    @69
    @15
    @70
    @69
    ve
    cE
    @7
    @9
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
    @1
    crab
    #
    @70
    crp
    @14
    cvv
    @69
    vb
    cA
    ve
    crp
    @7
    vb
    cv
    #
    @8
    cfv
    #
    @72
    cxad
    co
    #
    cle
    wbr
    #
    vi
    @76
    cC
    cfv
    #
    crab
    #
    cmpt
    #
    ve
    crp
    @75
    cmpt
    #
    @55
    cD
    cvv
    cD
    vb
    @55
    @82
    cmpt
    #
    wceq
    @69
    cD
    va
    @55
    ve
    crp
    @7
    @51
    @8
    cfv
    #
    @72
    cxad
    co
    #
    cle
    wbr
    #
    vi
    @51
    cC
    cfv
    #
    crab
    #
    cmpt
    #
    cmpt
    @84
    ovncvrrp.d
    va
    vb
    @55
    @90
    @82
    vb
    @90
    nfcv
    va
    ve
    crp
    @81
    va
    crp
    nfcv
    @79
    va
    vi
    @80
    @79
    va
    nfv
    va
    @76
    cC
    va
    cC
    @56
    ovncvrrp.c
    va
    @55
    @53
    nfmpt1
    nfcxfr
    va
    @76
    nfcv
    nffv
    nfrab
    nfmpt
    @51
    @76
    wceq
    #
    ve
    crp
    @89
    @81
    @91
    @87
    @79
    vi
    @88
    @80
    @91
    @0
    @88
    wcel
    @0
    @80
    wcel
    #
    @87
    @79
    @91
    @88
    @80
    @0
    @51
    @76
    cC
    fveq2
    eleq2d
    @91
    @86
    @78
    @7
    cle
    @91
    @85
    @77
    @72
    cxad
    @51
    @76
    @8
    fveq2
    oveq1d
    breq2d
    anbi12d
    rabbidva2
    mpteq2dv
    cbvmpt
    eqtri
    a1i
    @76
    cA
    wceq
    #
    @82
    @83
    wceq
    @69
    @93
    ve
    crp
    @81
    @75
    @93
    @79
    @74
    vi
    @80
    @1
    @93
    @92
    @2
    @79
    @74
    @93
    @80
    @1
    @0
    @76
    cA
    cC
    fveq2
    eleq2d
    @93
    @78
    @73
    @7
    cle
    @93
    @77
    @9
    @72
    cxad
    @76
    cA
    @8
    fveq2
    oveq1d
    breq2d
    anbi12d
    rabbidva2
    mpteq2dv
    adantl
    wph
    @58
    @12
    @60
    adantr
    @83
    cvv
    wcel
    @69
    ve
    crp
    @75
    rpex
    mptex
    a1i
    fvmptd
    @72
    cE
    wceq
    #
    @75
    @70
    wceq
    @69
    @94
    @74
    @11
    vi
    @1
    @94
    @73
    @10
    @7
    cle
    @72
    cE
    @9
    cxad
    oveq2
    breq2d
    rabbidv
    adantl
    wph
    cE
    crp
    wcel
    @12
    ovncvrrp.e
    adantr
    @70
    cvv
    wcel
    @69
    @11
    vi
    @1
    cA
    cC
    fvex
    rabex
    a1i
    fvmptd
    eqcomd
    eleqtrd
    ex
    eximdv
    mpd
end
