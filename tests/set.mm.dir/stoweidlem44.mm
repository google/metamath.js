include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "wa.mm"
include "wral.mm"
include "wceq.mm"
include "clt.mm"
include "cdif.mm"
include "w3a.mm"
include "wex.mm"
include "wrex.mm"
include "cfz.mm"
include "co.mm"
include "csu.mm"
include "cmpt.mm"
include "cdiv.mm"
include "eqid.mm"
include "nnrecred.mm"
include "wf.mm"
include "wss.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "fss.mm"
include "sylancl.mm"
include "ccn.mm"
include "sselda.mm"
include "fcnre.mm"
include "stoweidlem32.mm"
include "stoweidlem38.mm"
include "ex.mm"
include "ralrimi.mm"
include "stoweidlem37.mm"
include "cmul.mm"
include "nfv.mm"
include "nfan.mm"
include "r19.21bi.mm"
include "df-rex.mm"
include "sylib.mm"
include "cr.mm"
include "ad2antrr.mm"
include "simpll.mm"
include "eldifi.mm"
include "ad2antlr.mm"
include "fzfid.mm"
include "stoweidlem15.mm"
include "an32s.mm"
include "simp1d.mm"
include "fsumrecl.mm"
include "syl2anc.mm"
include "nnred.mm"
include "nngt0d.mm"
include "recgt0d.mm"
include "csn.mm"
include "caddc.mm"
include "0red.mm"
include "simprl.mm"
include "3jca.mm"
include "cfn.mm"
include "snfi.mm"
include "a1i.mm"
include "simpl1.mm"
include "simpl3.mm"
include "elsni.mm"
include "adantl.mm"
include "simpl2.mm"
include "eqeltrd.mm"
include "syl21anc.mm"
include "syl.mm"
include "readdcld.mm"
include "fzfi.mm"
include "diffi.mm"
include "mp1i.mm"
include "sylan2.mm"
include "00id.mm"
include "simprr.mm"
include "cc.mm"
include "recnd.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "sumsn.mm"
include "breqtrrd.mm"
include "ltadd2dd.mm"
include "syl5eqbrr.mm"
include "3adant2.mm"
include "simplr.mm"
include "simp2d.mm"
include "fsumge0.mm"
include "leadd1dd.mm"
include "ltletrd.mm"
include "cin.mm"
include "c0.mm"
include "wn.mm"
include "wi.mm"
include "eldifn.mm"
include "imnan.mm"
include "mpbi.mm"
include "elin.mm"
include "mtbir.mm"
include "nel0.mm"
include "cun.mm"
include "undif1.mm"
include "snssi.mm"
include "3ad2ant2.mm"
include "ssequn2.mm"
include "syl5req.mm"
include "3adantl2.mm"
include "fsumsplit.mm"
include "mulgt0d.mm"
include "exlimdd.mm"
include "stoweidlem30.mm"
include "eleq1.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfeq2.mm"
include "fveq1.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "ralbid.mm"
include "eqeq1d.mm"
include "3anbi123d.mm"
include "spcegv.mm"
include "mp2and.mm"
include "sylibr.mm"

theorem stoweidlem44
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let cG: class G
  let cJ: class J
  let cK: class K
  let cM: class M
  let cZ: class Z
  let vp: setvar p
  let vk: setvar k
  assume stoweidlem44.1: |- F/ j ph
  assume stoweidlem44.2: |- F/ t ph
  assume stoweidlem44.3: |- K = ( topGen ` ran (,) )
  assume stoweidlem44.4: |- Q = { h e. A | ( ( h ` Z ) = 0 /\ A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) ) }
  assume stoweidlem44.5: |- P = ( t e. T |-> ( ( 1 / M ) x. sum_ i e. ( 1 ... M ) ( ( G ` i ) ` t ) ) )
  assume stoweidlem44.6: |- ( ph -> M e. NN )
  assume stoweidlem44.7: |- ( ph -> G : ( 1 ... M ) --> Q )
  assume stoweidlem44.8: |- ( ph -> A. t e. ( T \ U ) E. j e. ( 1 ... M ) 0 < ( ( G ` j ) ` t ) )
  assume stoweidlem44.9: |- T = U. J
  assume stoweidlem44.10: |- ( ph -> A C_ ( J Cn K ) )
  assume stoweidlem44.11: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem44.12: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem44.13: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )
  assume stoweidlem44.14: |- ( ph -> Z e. T )

  disjoint f g
  disjoint f i
  disjoint f t
  disjoint G f
  disjoint g i
  disjoint g t
  disjoint G g
  disjoint i t
  disjoint G i
  disjoint G t
  disjoint f j
  disjoint i j
  disjoint j t
  disjoint G j
  disjoint A f
  disjoint A g
  disjoint M f
  disjoint M g
  disjoint M i
  disjoint M t
  disjoint T f
  disjoint T g
  disjoint T i
  disjoint T t
  disjoint f ph
  disjoint g ph
  disjoint i ph
  disjoint h i
  disjoint h j
  disjoint h t
  disjoint G h
  disjoint A h
  disjoint T h
  disjoint T j
  disjoint Z h
  disjoint Z i
  disjoint Z t
  disjoint j x
  disjoint M j
  disjoint t x
  disjoint M x
  disjoint U j
  disjoint p t
  disjoint T p
  disjoint A p
  disjoint P p
  disjoint U p
  disjoint Z p
  disjoint A x
  disjoint T x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> E. p e. A ( A. t e. T ( 0 <_ ( p ` t ) /\ ( p ` t ) <_ 1 ) /\ ( p ` Z ) = 0 /\ A. t e. ( T \ U ) 0 < ( p ` t ) ) )

  proof
    wph
    vp
    cv
    #
    cA
    wcel
    #
    cc0
    vt
    cv
    #
    @0
    cfv
    #
    cle
    wbr
    #
    @3
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    cZ
    @0
    cfv
    #
    cc0
    wceq
    #
    cc0
    @3
    clt
    wbr
    #
    vt
    cT
    cU
    cdif
    #
    wral
    #
    w3a
    #
    wa
    #
    vp
    wex
    #
    @13
    vp
    cA
    wrex
    wph
    cP
    cA
    wcel
    #
    cc0
    @2
    cP
    cfv
    #
    cle
    wbr
    #
    @17
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    cZ
    cP
    cfv
    #
    cc0
    wceq
    #
    cc0
    @17
    clt
    wbr
    #
    vt
    @11
    wral
    #
    w3a
    #
    @15
    wph
    vx
    vt
    cA
    cP
    cT
    vf
    vg
    vi
    vt
    cT
    c1
    cM
    cfz
    co
    #
    @2
    vi
    cv
    #
    cG
    cfv
    #
    cfv
    #
    vi
    csu
    #
    cmpt
    #
    cG
    vt
    cT
    c1
    cM
    cdiv
    co
    #
    cmpt
    #
    cM
    @33
    stoweidlem44.2
    stoweidlem44.5
    @32
    eqid
    @34
    eqid
    stoweidlem44.6
    wph
    cM
    stoweidlem44.6
    nnrecred
    #
    wph
    @27
    cQ
    cG
    wf
    cQ
    cA
    wss
    @27
    cA
    cG
    wf
    stoweidlem44.7
    cQ
    cZ
    vh
    cv
    #
    cfv
    cc0
    wceq
    cc0
    @2
    @36
    cfv
    #
    cle
    wbr
    @37
    c1
    cle
    wbr
    wa
    vt
    cT
    wral
    wa
    #
    vh
    cA
    crab
    cA
    stoweidlem44.4
    @38
    vh
    cA
    ssrab2
    eqsstri
    @27
    cQ
    cA
    cG
    fss
    sylancl
    stoweidlem44.11
    stoweidlem44.12
    stoweidlem44.13
    wph
    vf
    cv
    #
    cA
    wcel
    wa
    cJ
    cK
    ccn
    co
    #
    cT
    @39
    cJ
    cK
    stoweidlem44.3
    stoweidlem44.9
    @40
    eqid
    wph
    cA
    @40
    @39
    stoweidlem44.10
    sselda
    fcnre
    #
    stoweidlem32
    #
    wph
    @21
    @23
    @25
    wph
    @20
    vt
    cT
    stoweidlem44.2
    wph
    @2
    cT
    wcel
    #
    @20
    wph
    vt
    cA
    cP
    cQ
    @2
    cT
    vf
    vh
    vi
    cG
    cM
    cZ
    stoweidlem44.4
    stoweidlem44.5
    stoweidlem44.6
    stoweidlem44.7
    @41
    stoweidlem38
    ex
    ralrimi
    wph
    vt
    cA
    cP
    cQ
    cT
    vf
    vh
    vi
    cG
    cM
    cZ
    stoweidlem44.4
    stoweidlem44.5
    stoweidlem44.6
    stoweidlem44.7
    @41
    stoweidlem44.14
    stoweidlem37
    wph
    @24
    vt
    @11
    stoweidlem44.2
    wph
    @2
    @11
    wcel
    #
    @24
    wph
    @44
    wa
    #
    cc0
    @33
    @31
    cmul
    co
    #
    @17
    clt
    @45
    vj
    cv
    #
    @27
    wcel
    #
    cc0
    @2
    @47
    cG
    cfv
    #
    cfv
    #
    clt
    wbr
    #
    wa
    #
    cc0
    @46
    clt
    wbr
    #
    vj
    wph
    @44
    vj
    stoweidlem44.1
    @44
    vj
    nfv
    nfan
    @53
    vj
    nfv
    @45
    @51
    vj
    @27
    wrex
    #
    @52
    vj
    wex
    wph
    @54
    vt
    @11
    stoweidlem44.8
    r19.21bi
    @51
    vj
    @27
    df-rex
    sylib
    @45
    @52
    wa
    #
    @33
    @31
    wph
    @33
    cr
    wcel
    @44
    @52
    @35
    ad2antrr
    @55
    wph
    @43
    @31
    cr
    wcel
    wph
    @44
    @52
    simpll
    #
    @44
    @43
    wph
    @52
    @2
    cT
    cU
    eldifi
    #
    ad2antlr
    #
    wph
    @43
    wa
    #
    @27
    @30
    vi
    @59
    c1
    cM
    fzfid
    @59
    @28
    @27
    wcel
    #
    wa
    @30
    cr
    wcel
    #
    cc0
    @30
    cle
    wbr
    #
    @30
    c1
    cle
    wbr
    #
    wph
    @60
    @43
    @61
    @62
    @63
    w3a
    #
    wph
    vt
    cA
    cQ
    @2
    cT
    vf
    vh
    cG
    @28
    cM
    cZ
    stoweidlem44.4
    stoweidlem44.7
    @41
    stoweidlem15
    #
    an32s
    simp1d
    #
    fsumrecl
    syl2anc
    wph
    cc0
    @33
    clt
    wbr
    @44
    @52
    wph
    cM
    wph
    cM
    stoweidlem44.6
    nnred
    wph
    cM
    stoweidlem44.6
    nngt0d
    recgt0d
    ad2antrr
    @55
    cc0
    @27
    @47
    csn
    #
    cdif
    #
    @30
    vi
    csu
    #
    @67
    @30
    vi
    csu
    #
    caddc
    co
    #
    @31
    clt
    @55
    cc0
    cc0
    @70
    caddc
    co
    #
    @71
    @55
    0red
    #
    @55
    cc0
    @70
    @73
    @55
    wph
    @48
    @43
    w3a
    #
    @70
    cr
    wcel
    @55
    wph
    @48
    @43
    @56
    @45
    @48
    @51
    simprl
    #
    @58
    3jca
    #
    @74
    @67
    @30
    vi
    @67
    cfn
    wcel
    @74
    @47
    snfi
    a1i
    @74
    @28
    @67
    wcel
    #
    wa
    #
    wph
    @43
    @60
    @61
    wph
    @48
    @43
    @77
    simpl1
    wph
    @48
    @43
    @77
    simpl3
    @78
    @28
    @47
    @27
    @77
    @28
    @47
    wceq
    #
    @74
    @28
    @47
    elsni
    adantl
    wph
    @48
    @43
    @77
    simpl2
    eqeltrd
    @66
    syl21anc
    fsumrecl
    #
    syl
    #
    readdcld
    @55
    @69
    @70
    @55
    wph
    @43
    @69
    cr
    wcel
    #
    @56
    @58
    @59
    @68
    @30
    vi
    @27
    cfn
    wcel
    @68
    cfn
    wcel
    @59
    c1
    cM
    fzfi
    @27
    @67
    diffi
    mp1i
    #
    @28
    @68
    wcel
    #
    @59
    @60
    @61
    @28
    @27
    @67
    eldifi
    #
    @66
    sylan2
    #
    fsumrecl
    #
    syl2anc
    @81
    readdcld
    @55
    cc0
    cc0
    cc0
    caddc
    co
    @72
    clt
    00id
    @55
    cc0
    @70
    cc0
    @73
    @81
    @73
    @55
    cc0
    @50
    @70
    clt
    @45
    @48
    @51
    simprr
    @55
    @48
    @50
    cc
    wcel
    @70
    @50
    wceq
    @75
    @55
    @50
    @55
    wph
    @48
    @43
    @50
    cr
    wcel
    #
    @56
    @75
    @58
    wph
    @48
    wa
    @43
    wa
    @88
    cc0
    @50
    cle
    wbr
    @50
    c1
    cle
    wbr
    wph
    vt
    cA
    cQ
    @2
    cT
    vf
    vh
    cG
    @47
    cM
    cZ
    stoweidlem44.4
    stoweidlem44.7
    @41
    stoweidlem15
    simp1d
    syl21anc
    recnd
    @30
    @50
    vi
    @47
    @27
    @79
    @2
    @29
    @49
    @28
    @47
    cG
    fveq2
    fveq1d
    sumsn
    syl2anc
    breqtrrd
    ltadd2dd
    syl5eqbrr
    @55
    @74
    @72
    @71
    cle
    wbr
    @76
    @74
    cc0
    @69
    @70
    @74
    0red
    wph
    @43
    @82
    @48
    @87
    3adant2
    @80
    wph
    @43
    cc0
    @69
    cle
    wbr
    @48
    @59
    @68
    @30
    vi
    @83
    @86
    @59
    @84
    wa
    #
    @61
    @62
    @63
    @89
    wph
    @60
    @43
    @64
    wph
    @43
    @84
    simpll
    @84
    @60
    @59
    @85
    adantl
    wph
    @43
    @84
    simplr
    @65
    syl21anc
    simp2d
    fsumge0
    3adant2
    leadd1dd
    syl
    ltletrd
    @55
    @74
    @31
    @71
    wceq
    @76
    @74
    @68
    @67
    @30
    @27
    vi
    @68
    @67
    cin
    #
    c0
    wceq
    @74
    vx
    @90
    vx
    cv
    #
    @90
    wcel
    @91
    @68
    wcel
    #
    @91
    @67
    wcel
    #
    wa
    #
    @92
    @93
    wn
    wi
    @94
    wn
    @91
    @27
    @67
    eldifn
    @92
    @93
    imnan
    mpbi
    @91
    @68
    @67
    elin
    mtbir
    nel0
    a1i
    @74
    @68
    @67
    cun
    @27
    @67
    cun
    #
    @27
    @27
    @67
    undif1
    @74
    @67
    @27
    wss
    #
    @95
    @27
    wceq
    @48
    wph
    @96
    @43
    @47
    @27
    snssi
    3ad2ant2
    @67
    @27
    ssequn2
    sylib
    syl5req
    @74
    c1
    cM
    fzfid
    @74
    @60
    wa
    @30
    wph
    @43
    @60
    @61
    @48
    @66
    3adantl2
    recnd
    fsumsplit
    syl
    breqtrrd
    mulgt0d
    exlimdd
    @44
    wph
    @43
    @17
    @46
    wceq
    @57
    wph
    vt
    cA
    cP
    cQ
    @2
    cT
    vf
    vh
    vi
    cG
    cM
    cZ
    stoweidlem44.4
    stoweidlem44.5
    stoweidlem44.6
    stoweidlem44.7
    @41
    stoweidlem30
    sylan2
    breqtrrd
    ex
    ralrimi
    3jca
    wph
    @16
    @16
    @26
    wa
    #
    @15
    wi
    @42
    @14
    @97
    vp
    cP
    cA
    @0
    cP
    wceq
    #
    @1
    @16
    @13
    @26
    @0
    cP
    cA
    eleq1
    @98
    @7
    @21
    @9
    @23
    @12
    @25
    @98
    @6
    @20
    vt
    cT
    vt
    @0
    cP
    vt
    cP
    vt
    cT
    @46
    cmpt
    stoweidlem44.5
    vt
    cT
    @46
    nfmpt1
    nfcxfr
    nfeq2
    #
    @98
    @4
    @18
    @5
    @19
    @98
    @3
    @17
    cc0
    cle
    @2
    @0
    cP
    fveq1
    #
    breq2d
    @98
    @3
    @17
    c1
    cle
    @100
    breq1d
    anbi12d
    ralbid
    @98
    @8
    @22
    cc0
    cZ
    @0
    cP
    fveq1
    eqeq1d
    @98
    @10
    @24
    vt
    @11
    @99
    @98
    @3
    @17
    cc0
    clt
    @100
    breq2d
    ralbid
    3anbi123d
    anbi12d
    spcegv
    syl
    mp2and
    @13
    vp
    cA
    df-rex
    sylibr
end
