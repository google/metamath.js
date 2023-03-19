include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cres.mm"
include "cdif.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "cvv.mm"
include "resexg.mm"
include "adantl.mm"
include "simpr.mm"
include "difexg.mm"
include "3ad2ant1.mm"
include "snex.mm"
include "xpexg.mm"
include "sylancl.mm"
include "adantr.mm"
include "unexg.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "wceq.mm"
include "ccnv.mm"
include "cima.mm"
include "rabeq2i.mm"
include "anbi1i.mm"
include "simprr.mm"
include "wf.mm"
include "simprll.mm"
include "elmapi.mm"
include "syl.mm"
include "simp3.mm"
include "ad2antrr.mm"
include "fssresd.mm"
include "wb.mm"
include "simp2.mm"
include "simp1.mm"
include "ssexd.mm"
include "elmapg.mm"
include "mpbird.mm"
include "eqeltrd.mm"
include "undif.mm"
include "biimpi.mm"
include "reseq2d.mm"
include "wfn.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "eqtr2d.mm"
include "resundi.mm"
include "syl6eq.mm"
include "eqcomd.mm"
include "csupp.mm"
include "cin.mm"
include "simprlr.mm"
include "simplr.mm"
include "eqid.mm"
include "ffs2.mm"
include "syl3anc.mm"
include "sseqin2.mm"
include "3sstr4d.mm"
include "c0.mm"
include "simpl.mm"
include "inundif.mm"
include "fneq2i.mm"
include "sylibr.mm"
include "vex.mm"
include "a1i.mm"
include "inindif.mm"
include "fnsuppres.mm"
include "syl121anc.mm"
include "mpbid.mm"
include "uneq12d.mm"
include "eqtrd.mm"
include "jca.mm"
include "ad2antrl.mm"
include "fconst6g.mm"
include "disjdif.mm"
include "fun2.mm"
include "syl21anc.mm"
include "feq12d.mm"
include "biimpar.mm"
include "cfv.mm"
include "fveq1d.mm"
include "fconstg.mm"
include "ad3antlr.mm"
include "fvun2.mm"
include "syl112anc.mm"
include "fvconst.mm"
include "3eqtrd.mm"
include "suppss.mm"
include "eqsstr3d.mm"
include "reseq1d.mm"
include "res0.mm"
include "eqtr4i.mm"
include "reseq2i.mm"
include "3eqtr4ri.mm"
include "fresaunres1.mm"
include "jca31.mm"
include "impbida.mm"
include "syl5bb.mm"
include "f1od.mm"

theorem resf1o
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cZ: class Z
  let vg: setvar g
  let vx: setvar x
  assume resf1o.1: |- X = { f e. ( B ^m A ) | ( `' f " ( B \ { Z } ) ) C_ C }
  assume resf1o.2: |- F = ( f e. X |-> ( f |` C ) )

  disjoint A f
  disjoint B f
  disjoint C f
  disjoint V f
  disjoint W f
  disjoint X f
  disjoint Z f
  disjoint f g
  disjoint f x
  disjoint g x
  disjoint A g
  disjoint A x
  disjoint B g
  disjoint B x
  disjoint C g
  disjoint C x
  disjoint V g
  disjoint V x
  disjoint W g
  disjoint W x
  disjoint X g
  disjoint Z g
  disjoint Z x
  assert |- ( ( ( A e. V /\ B e. W /\ C C_ A ) /\ Z e. B ) -> F : X -1-1-onto-> ( B ^m C ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cC
    cA
    wss
    #
    w3a
    #
    cZ
    cB
    wcel
    #
    wa
    #
    vf
    vg
    cX
    cB
    cC
    cmap
    co
    #
    vf
    cv
    #
    cC
    cres
    #
    vg
    cv
    #
    cA
    cC
    cdif
    #
    cZ
    csn
    #
    cxp
    #
    cun
    #
    cF
    cvv
    cvv
    resf1o.2
    @7
    cX
    wcel
    #
    @8
    cvv
    wcel
    @5
    @7
    cC
    cX
    resexg
    adantl
    @3
    @9
    @6
    wcel
    #
    @13
    cvv
    wcel
    #
    @4
    @3
    @15
    wa
    @15
    @12
    cvv
    wcel
    #
    @16
    @3
    @15
    simpr
    @3
    @17
    @15
    @3
    @10
    cvv
    wcel
    #
    @11
    cvv
    wcel
    @17
    @0
    @1
    @18
    @2
    cA
    cC
    cV
    difexg
    3ad2ant1
    cZ
    snex
    @10
    @11
    cvv
    cvv
    xpexg
    sylancl
    adantr
    @9
    @12
    @6
    cvv
    unexg
    syl2anc
    adantlr
    @14
    @9
    @8
    wceq
    #
    wa
    @7
    cB
    cA
    cmap
    co
    #
    wcel
    #
    @7
    ccnv
    cB
    @11
    cdif
    #
    cima
    #
    cC
    wss
    #
    wa
    #
    @19
    wa
    #
    @5
    @15
    @7
    @13
    wceq
    #
    wa
    #
    @14
    @25
    @19
    @24
    vf
    cX
    @20
    resf1o.1
    rabeq2i
    anbi1i
    @5
    @26
    @28
    @5
    @26
    wa
    #
    @15
    @27
    @29
    @9
    @8
    @6
    @5
    @25
    @19
    simprr
    #
    @29
    @8
    @6
    wcel
    #
    cC
    cB
    @8
    wf
    #
    @29
    cA
    cB
    cC
    @7
    @29
    @21
    cA
    cB
    @7
    wf
    #
    @5
    @21
    @24
    @19
    simprll
    #
    @7
    cB
    cA
    elmapi
    #
    syl
    #
    @3
    @2
    @4
    @26
    @0
    @1
    @2
    simp3
    #
    ad2antrr
    #
    fssresd
    @3
    @31
    @32
    wb
    #
    @4
    @26
    @3
    @1
    cC
    cvv
    wcel
    @39
    @0
    @1
    @2
    simp2
    #
    @3
    cC
    cA
    cV
    @0
    @1
    @2
    simp1
    #
    @37
    ssexd
    cB
    cC
    @8
    cW
    cvv
    elmapg
    syl2anc
    ad2antrr
    mpbird
    eqeltrd
    @29
    @7
    @8
    @7
    @10
    cres
    #
    cun
    #
    @13
    @29
    @7
    @7
    cC
    @10
    cun
    #
    cres
    #
    @43
    @29
    @45
    @7
    cA
    cres
    #
    @7
    @29
    @2
    @45
    @46
    wceq
    @38
    @2
    @44
    cA
    @7
    @2
    @44
    cA
    wceq
    #
    cC
    cA
    undif
    biimpi
    #
    reseq2d
    syl
    @29
    @33
    @7
    cA
    wfn
    #
    @46
    @7
    wceq
    @36
    cA
    cB
    @7
    ffn
    #
    cA
    @7
    fnresdm
    3syl
    eqtr2d
    @7
    cC
    @10
    resundi
    syl6eq
    @29
    @8
    @9
    @42
    @12
    @29
    @9
    @8
    @30
    eqcomd
    @29
    @7
    cZ
    csupp
    co
    #
    cA
    cC
    cin
    #
    wss
    #
    @42
    @12
    wceq
    #
    @29
    @23
    cC
    @51
    @52
    @5
    @21
    @24
    @19
    simprlr
    @29
    @0
    @4
    @33
    @51
    @23
    wceq
    #
    @3
    @0
    @4
    @26
    @41
    ad2antrr
    @3
    @4
    @26
    simplr
    #
    @36
    cA
    cB
    @22
    @7
    cV
    cB
    cZ
    @22
    eqid
    ffs2
    #
    syl3anc
    @29
    @2
    @52
    cC
    wceq
    #
    @38
    @2
    @58
    cC
    cA
    sseqin2
    biimpi
    syl
    3sstr4d
    @29
    @21
    @4
    @53
    @54
    wb
    #
    @34
    @56
    @21
    @4
    wa
    #
    @7
    @52
    @10
    cun
    #
    wfn
    #
    @7
    cvv
    wcel
    #
    @4
    @52
    @10
    cin
    c0
    wceq
    #
    @59
    @60
    @49
    @62
    @60
    @21
    @33
    @49
    @21
    @4
    simpl
    @35
    @50
    3syl
    @61
    cA
    @7
    cA
    cC
    inundif
    fneq2i
    sylibr
    @63
    @60
    vf
    vex
    a1i
    @21
    @4
    simpr
    @64
    @60
    cA
    cC
    inindif
    a1i
    @52
    @10
    @7
    cB
    cvv
    cZ
    fnsuppres
    syl121anc
    syl2anc
    mpbid
    uneq12d
    eqtrd
    jca
    @5
    @28
    wa
    #
    @21
    @24
    @19
    @65
    @1
    @0
    @33
    @21
    @3
    @1
    @4
    @28
    @40
    ad2antrr
    @3
    @0
    @4
    @28
    @41
    ad2antrr
    #
    @65
    @44
    cB
    @13
    wf
    #
    @33
    @65
    cC
    cB
    @9
    wf
    #
    @10
    cB
    @12
    wf
    #
    cC
    @10
    cin
    #
    c0
    wceq
    #
    @67
    @15
    @68
    @5
    @27
    @9
    cB
    cC
    elmapi
    ad2antrl
    #
    @65
    @4
    @69
    @3
    @4
    @28
    simplr
    #
    @10
    cZ
    cB
    fconst6g
    syl
    #
    @71
    @65
    cC
    cA
    disjdif
    #
    a1i
    cC
    @10
    cB
    @9
    @12
    fun2
    syl21anc
    @65
    @44
    cA
    cB
    @13
    @7
    @65
    @7
    @13
    @5
    @15
    @27
    simprr
    #
    eqcomd
    @65
    @2
    @47
    @3
    @2
    @4
    @28
    @37
    ad2antrr
    @48
    syl
    feq12d
    mpbid
    #
    @1
    @0
    wa
    @21
    @33
    cB
    cA
    @7
    cW
    cV
    elmapg
    biimpar
    syl21anc
    @65
    @23
    @51
    cC
    @65
    @0
    @4
    @33
    @55
    @66
    @73
    @77
    @57
    syl3anc
    @65
    cA
    cB
    vx
    @7
    cC
    cZ
    @77
    @65
    vx
    cv
    #
    @10
    wcel
    #
    wa
    #
    @78
    @7
    cfv
    @78
    @13
    cfv
    #
    @78
    @12
    cfv
    #
    cZ
    @80
    @78
    @7
    @13
    @65
    @27
    @79
    @76
    adantr
    fveq1d
    @80
    @9
    cC
    wfn
    #
    @12
    @10
    wfn
    #
    @71
    @79
    @81
    @82
    wceq
    @80
    @68
    @83
    @65
    @68
    @79
    @72
    adantr
    cC
    cB
    @9
    ffn
    syl
    @80
    @10
    @11
    @12
    wf
    #
    @84
    @4
    @85
    @3
    @28
    @79
    @10
    cZ
    cB
    fconstg
    ad3antlr
    #
    @10
    @11
    @12
    ffn
    syl
    @71
    @80
    @75
    a1i
    @65
    @79
    simpr
    #
    cC
    @10
    @9
    @12
    @78
    fvun2
    syl112anc
    @80
    @85
    @79
    @82
    cZ
    wceq
    @86
    @87
    @10
    cZ
    @78
    @12
    fvconst
    syl2anc
    3eqtrd
    suppss
    eqsstr3d
    @65
    @8
    @13
    cC
    cres
    #
    @9
    @65
    @7
    @13
    cC
    @76
    reseq1d
    @65
    @68
    @69
    @9
    @70
    cres
    #
    @12
    @70
    cres
    #
    wceq
    #
    @88
    @9
    wceq
    @72
    @74
    @91
    @65
    @12
    c0
    cres
    #
    @9
    c0
    cres
    #
    @90
    @89
    @92
    c0
    @93
    @12
    res0
    @9
    res0
    eqtr4i
    @70
    c0
    @12
    @75
    reseq2i
    @70
    c0
    @9
    @75
    reseq2i
    3eqtr4ri
    a1i
    cC
    @10
    cB
    @9
    @12
    fresaunres1
    syl3anc
    eqtr2d
    jca31
    impbida
    syl5bb
    f1od
end
