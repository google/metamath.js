include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "ccom.mm"
include "cima.mm"
include "clt.mm"
include "cres.mm"
include "wiso.mm"
include "wa.mm"
include "ccnv.mm"
include "wo.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cpw.mm"
include "wrex.mm"
include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cmin.mm"
include "cmul.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "nn0mulcld.mm"
include "syl5eqel.mm"
include "nn0p1nn.mm"
include "cr.mm"
include "wf1.mm"
include "f1co.mm"
include "syl2anc.mm"
include "nn0red.mm"
include "ltp1d.mm"
include "syl5eqbrr.mm"
include "erdsze.mm"
include "wss.mm"
include "wi.mm"
include "selpw.mm"
include "crn.mm"
include "imassrn.mm"
include "wf.mm"
include "f1f.mm"
include "frn.mm"
include "syl5ss.mm"
include "cvv.mm"
include "wb.mm"
include "reex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "elpw2g.mm"
include "mpbird.mm"
include "adantr.mm"
include "wceq.mm"
include "cen.mm"
include "vex.mm"
include "f1imaen.mm"
include "sylan.mm"
include "cfn.mm"
include "fzfid.mm"
include "simpr.mm"
include "ssfi.mm"
include "enfii.mm"
include "hashen.mm"
include "breq2d.mm"
include "biimprd.mm"
include "wral.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "sseldd.mm"
include "simprr.mm"
include "isorel.mm"
include "syl12anc.mm"
include "biimpd.mm"
include "ralrimivva.mm"
include "wor.mm"
include "elfznn.mm"
include "nnred.mm"
include "ssriv.mm"
include "a1i.mm"
include "ltso.mm"
include "soss.mm"
include "mpisyl.mm"
include "soisores.mm"
include "syl22anc.mm"
include "isocnv.mm"
include "isotr.mm"
include "ex.mm"
include "resco.mm"
include "coeq1i.mm"
include "coass.mm"
include "eqtri.mm"
include "cid.mm"
include "wf1o.mm"
include "f1ores.mm"
include "f1ococnv2.mm"
include "coeq2d.mm"
include "coires1.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "isoeq1.mm"
include "imaco.mm"
include "isoeq5.mm"
include "ax-mp.mm"
include "syl6bb.mm"
include "sylibd.mm"
include "anim12d.mm"
include "orim12d.mm"
include "fveq2.mm"
include "reseq2.mm"
include "isoeq4.mm"
include "imaeq2.mm"
include "3bitrd.mm"
include "anbi12d.mm"
include "orbi12d.mm"
include "rspcev.mm"
include "syl6an.mm"
include "sylan2b.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem erdsze2lem2
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cN: class N
  let vs: setvar s
  let vf: setvar f
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  assume erdsze2.r: |- ( ph -> R e. NN )
  assume erdsze2.s: |- ( ph -> S e. NN )
  assume erdsze2.f: |- ( ph -> F : A -1-1-> RR )
  assume erdsze2.a: |- ( ph -> A C_ RR )
  assume erdsze2lem.n: |- N = ( ( R - 1 ) x. ( S - 1 ) )
  assume erdsze2lem.l: |- ( ph -> N < ( # ` A ) )
  assume erdsze2lem.g: |- ( ph -> G : ( 1 ... ( N + 1 ) ) -1-1-> A )
  assume erdsze2lem.i: |- ( ph -> G Isom < , < ( ( 1 ... ( N + 1 ) ) , ran G ) )

  disjoint A s
  disjoint F s
  disjoint G s
  disjoint R s
  disjoint S s
  disjoint N s
  disjoint ph s
  disjoint f s
  disjoint f t
  disjoint A f
  disjoint s t
  disjoint A t
  disjoint F f
  disjoint F t
  disjoint s x
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint G t
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint R f
  disjoint R t
  disjoint S f
  disjoint S t
  disjoint f x
  disjoint f y
  disjoint N f
  disjoint N t
  disjoint N x
  disjoint N y
  disjoint f ph
  disjoint ph t
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> E. s e. ~P A ( ( R <_ ( # ` s ) /\ ( F |` s ) Isom < , < ( s , ( F " s ) ) ) \/ ( S <_ ( # ` s ) /\ ( F |` s ) Isom < , `' < ( s , ( F " s ) ) ) ) )

  proof
    wph
    cR
    vt
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    @0
    cF
    cG
    ccom
    #
    @0
    cima
    #
    clt
    clt
    @3
    @0
    cres
    #
    wiso
    #
    wa
    #
    cS
    @1
    cle
    wbr
    #
    @0
    @4
    clt
    clt
    ccnv
    #
    @5
    wiso
    #
    wa
    #
    wo
    #
    vt
    c1
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    cpw
    #
    wrex
    cR
    vs
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    @16
    cF
    @16
    cima
    #
    clt
    clt
    cF
    @16
    cres
    #
    wiso
    #
    wa
    #
    cS
    @17
    cle
    wbr
    #
    @16
    @19
    clt
    @9
    @20
    wiso
    #
    wa
    #
    wo
    #
    vs
    cA
    cpw
    #
    wrex
    #
    wph
    cR
    cS
    @3
    @13
    vt
    wph
    cN
    cn0
    wcel
    @13
    cn
    wcel
    wph
    cN
    cR
    c1
    cmin
    co
    #
    cS
    c1
    cmin
    co
    #
    cmul
    co
    #
    cn0
    erdsze2lem.n
    wph
    @29
    @30
    wph
    cR
    cn
    wcel
    @29
    cn0
    wcel
    erdsze2.r
    cR
    nnm1nn0
    syl
    wph
    cS
    cn
    wcel
    @30
    cn0
    wcel
    erdsze2.s
    cS
    nnm1nn0
    syl
    nn0mulcld
    syl5eqel
    #
    cN
    nn0p1nn
    syl
    wph
    cA
    cr
    cF
    wf1
    @14
    cA
    cG
    wf1
    #
    @14
    cr
    @3
    wf1
    erdsze2.f
    erdsze2lem.g
    @14
    cA
    cr
    cF
    cG
    f1co
    syl2anc
    erdsze2.r
    erdsze2.s
    wph
    @31
    cN
    @13
    clt
    erdsze2lem.n
    wph
    cN
    wph
    cN
    @32
    nn0red
    ltp1d
    syl5eqbrr
    erdsze
    wph
    @12
    @28
    vt
    @15
    @0
    @15
    wcel
    wph
    @0
    @14
    wss
    #
    @12
    @28
    wi
    vt
    @14
    selpw
    wph
    @34
    wa
    #
    cG
    @0
    cima
    #
    @27
    wcel
    #
    @12
    cR
    @36
    chash
    cfv
    #
    cle
    wbr
    #
    @36
    cF
    @36
    cima
    #
    clt
    clt
    cF
    @36
    cres
    #
    wiso
    #
    wa
    #
    cS
    @38
    cle
    wbr
    #
    @36
    @40
    clt
    @9
    @41
    wiso
    #
    wa
    #
    wo
    #
    @28
    wph
    @37
    @34
    wph
    @37
    @36
    cA
    wss
    #
    wph
    @36
    cG
    crn
    #
    cA
    cG
    @0
    imassrn
    wph
    @14
    cA
    cG
    wf
    #
    @49
    cA
    wss
    wph
    @33
    @50
    erdsze2lem.g
    @14
    cA
    cG
    f1f
    syl
    #
    @14
    cA
    cG
    frn
    syl
    syl5ss
    wph
    cA
    cvv
    wcel
    #
    @37
    @48
    wb
    wph
    cA
    cr
    wss
    #
    cr
    cvv
    wcel
    @52
    erdsze2.a
    reex
    cA
    cr
    cvv
    ssexg
    sylancl
    @36
    cA
    cvv
    elpw2g
    syl
    mpbird
    adantr
    @35
    @7
    @43
    @11
    @46
    @35
    @2
    @39
    @6
    @42
    @35
    @39
    @2
    @35
    @38
    @1
    cR
    cle
    @35
    @38
    @1
    wceq
    #
    @36
    @0
    cen
    wbr
    #
    wph
    @33
    @34
    @55
    erdsze2lem.g
    @14
    cA
    @0
    cG
    vt
    vex
    f1imaen
    sylan
    #
    @35
    @36
    cfn
    wcel
    #
    @0
    cfn
    wcel
    #
    @54
    @55
    wb
    @35
    @58
    @55
    @57
    @35
    @14
    cfn
    wcel
    @34
    @58
    @35
    c1
    @13
    fzfid
    wph
    @34
    simpr
    #
    @14
    @0
    ssfi
    syl2anc
    #
    @56
    @36
    @0
    enfii
    syl2anc
    @60
    @36
    @0
    hashen
    syl2anc
    mpbird
    #
    breq2d
    biimprd
    @35
    @6
    @36
    @4
    clt
    clt
    @5
    cG
    @0
    cres
    #
    ccnv
    #
    ccom
    #
    wiso
    #
    @42
    @35
    @36
    @0
    clt
    clt
    @63
    wiso
    #
    @6
    @65
    wi
    @35
    @0
    @36
    clt
    clt
    @62
    wiso
    #
    @66
    @35
    @67
    vx
    cv
    #
    vy
    cv
    #
    clt
    wbr
    #
    @68
    cG
    cfv
    @69
    cG
    cfv
    clt
    wbr
    #
    wi
    #
    vy
    @0
    wral
    vx
    @0
    wral
    #
    @35
    @72
    vx
    vy
    @0
    @0
    @35
    @68
    @0
    wcel
    #
    @69
    @0
    wcel
    #
    wa
    #
    wa
    #
    @70
    @71
    @77
    @14
    @49
    clt
    clt
    cG
    wiso
    #
    @68
    @14
    wcel
    @69
    @14
    wcel
    @70
    @71
    wb
    wph
    @78
    @34
    @76
    erdsze2lem.i
    ad2antrr
    @77
    @0
    @14
    @68
    @35
    @34
    @76
    @59
    adantr
    #
    @35
    @74
    @75
    simprl
    sseldd
    @77
    @0
    @14
    @69
    @79
    @35
    @74
    @75
    simprr
    sseldd
    @14
    @49
    @68
    @69
    clt
    clt
    cG
    isorel
    syl12anc
    biimpd
    ralrimivva
    @35
    @14
    clt
    wor
    #
    cA
    clt
    wor
    #
    @50
    @34
    @67
    @73
    wb
    @35
    @14
    cr
    wss
    #
    cr
    clt
    wor
    #
    @80
    @82
    @35
    vt
    @14
    cr
    @0
    @14
    wcel
    @0
    @0
    @13
    elfznn
    nnred
    ssriv
    a1i
    ltso
    @14
    cr
    clt
    soss
    mpisyl
    @35
    @53
    @83
    @81
    wph
    @53
    @34
    erdsze2.a
    adantr
    ltso
    cA
    cr
    clt
    soss
    mpisyl
    wph
    @50
    @34
    @51
    adantr
    @59
    vx
    vy
    @0
    @14
    cA
    clt
    clt
    cG
    soisores
    syl22anc
    mpbird
    @0
    @36
    clt
    clt
    @62
    isocnv
    syl
    #
    @66
    @6
    @65
    @36
    @0
    @4
    clt
    clt
    clt
    @5
    @63
    isotr
    ex
    syl
    @35
    @65
    @36
    @4
    clt
    clt
    @41
    wiso
    #
    @42
    @35
    @64
    @41
    wceq
    #
    @65
    @85
    wb
    @35
    @64
    cF
    @62
    @63
    ccom
    #
    ccom
    #
    @41
    @64
    cF
    @62
    ccom
    #
    @63
    ccom
    @88
    @5
    @89
    @63
    cF
    cG
    @0
    resco
    coeq1i
    cF
    @62
    @63
    coass
    eqtri
    @35
    @88
    cF
    cid
    @36
    cres
    #
    ccom
    @41
    @35
    @87
    @90
    cF
    @35
    @0
    @36
    @62
    wf1o
    #
    @87
    @90
    wceq
    wph
    @33
    @34
    @91
    erdsze2lem.g
    @14
    cA
    @0
    cG
    f1ores
    sylan
    @0
    @36
    @62
    f1ococnv2
    syl
    coeq2d
    cF
    @36
    coires1
    syl6eq
    syl5eq
    #
    @36
    @4
    clt
    clt
    @41
    @64
    isoeq1
    syl
    @4
    @40
    wceq
    #
    @85
    @42
    wb
    cF
    cG
    @0
    imaco
    #
    @36
    @4
    @40
    clt
    clt
    @41
    isoeq5
    ax-mp
    syl6bb
    sylibd
    anim12d
    @35
    @8
    @44
    @10
    @45
    @35
    @44
    @8
    @35
    @38
    @1
    cS
    cle
    @61
    breq2d
    biimprd
    @35
    @10
    @36
    @4
    clt
    @9
    @64
    wiso
    #
    @45
    @35
    @66
    @10
    @95
    wi
    @84
    @66
    @10
    @95
    @36
    @0
    @4
    clt
    clt
    @9
    @5
    @63
    isotr
    ex
    syl
    @35
    @95
    @36
    @4
    clt
    @9
    @41
    wiso
    #
    @45
    @35
    @86
    @95
    @96
    wb
    @92
    @36
    @4
    clt
    @9
    @41
    @64
    isoeq1
    syl
    @93
    @96
    @45
    wb
    @94
    @36
    @4
    @40
    clt
    @9
    @41
    isoeq5
    ax-mp
    syl6bb
    sylibd
    anim12d
    orim12d
    @26
    @47
    vs
    @36
    @27
    @16
    @36
    wceq
    #
    @22
    @43
    @25
    @46
    @97
    @18
    @39
    @21
    @42
    @97
    @17
    @38
    cR
    cle
    @16
    @36
    chash
    fveq2
    #
    breq2d
    @97
    @21
    @16
    @19
    clt
    clt
    @41
    wiso
    #
    @36
    @19
    clt
    clt
    @41
    wiso
    #
    @42
    @97
    @20
    @41
    wceq
    #
    @21
    @99
    wb
    @16
    @36
    cF
    reseq2
    #
    @16
    @19
    clt
    clt
    @41
    @20
    isoeq1
    syl
    @16
    @19
    @36
    clt
    clt
    @41
    isoeq4
    @97
    @19
    @40
    wceq
    #
    @100
    @42
    wb
    @16
    @36
    cF
    imaeq2
    #
    @36
    @19
    @40
    clt
    clt
    @41
    isoeq5
    syl
    3bitrd
    anbi12d
    @97
    @23
    @44
    @24
    @45
    @97
    @17
    @38
    cS
    cle
    @98
    breq2d
    @97
    @24
    @16
    @19
    clt
    @9
    @41
    wiso
    #
    @36
    @19
    clt
    @9
    @41
    wiso
    #
    @45
    @97
    @101
    @24
    @105
    wb
    @102
    @16
    @19
    clt
    @9
    @41
    @20
    isoeq1
    syl
    @16
    @19
    @36
    clt
    @9
    @41
    isoeq4
    @97
    @103
    @106
    @45
    wb
    @104
    @36
    @19
    @40
    clt
    @9
    @41
    isoeq5
    syl
    3bitrd
    anbi12d
    orbi12d
    rspcev
    syl6an
    sylan2b
    rexlimdva
    mpd
end
