include "cfv.mm"
include "co.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wrel.mm"
include "dihvalrel.mm"
include "syl.mm"
include "cv.mm"
include "wbr.mm"
include "wceq.mm"
include "cop.mm"
include "ccom.mm"
include "wex.mm"
include "ccnv.mm"
include "wrex.mm"
include "adantr.mm"
include "wn.mm"
include "lhpocnel2.mm"
include "ltrniotacl.mm"
include "syl3anc.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "ltrnco.mm"
include "simprll.mm"
include "simprlr.mm"
include "dihjatcclem3.mm"
include "breqtrrd.mm"
include "tendoex.mm"
include "syl121anc.mm"
include "df-rex.mm"
include "sylib.mm"
include "eqidd.mm"
include "simprl.mm"
include "wb.mm"
include "ad2antrr.mm"
include "fvex.mm"
include "vex.mm"
include "dihopelvalcqat.mm"
include "mpbir2and.mm"
include "tendoicl.mm"
include "tendospdi1.mm"
include "syl13anc.mm"
include "simprr.mm"
include "tendoi2.mm"
include "tendocnv.mm"
include "eqtr2d.mm"
include "coeq2d.mm"
include "3eqtr3d.mm"
include "simplrr.mm"
include "tendoipl2.mm"
include "eqtr4d.mm"
include "cvv.mm"
include "wi.mm"
include "opeq1.mm"
include "eleq1d.mm"
include "anbi1d.mm"
include "coeq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "coeq2.mm"
include "opeq2.mm"
include "oveq2.mm"
include "syl3an9b.mm"
include "spc3egv.mm"
include "mp3an.mm"
include "syl22anc.mm"
include "ex.mm"
include "eximdv.mm"
include "excom.mm"
include "syl6ib.mm"
include "mpd.mm"
include "cdib.mm"
include "clat.mm"
include "simpld.mm"
include "hllat.mm"
include "hlatjcl.mm"
include "simprd.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl5eqel.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "eqid.mm"
include "dihvalb.mm"
include "syl12anc.mm"
include "eleq2d.mm"
include "dibopelval3.mm"
include "bitrd.mm"
include "clss.mm"
include "atbase.mm"
include "dihopellsm.mm"
include "3imtr4d.mm"
include "relssdv.mm"

theorem dihjatcclem4
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let cE: class E
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let vt: setvar t
  let vf: setvar f
  let vs: setvar s
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  assume dihjatcclem.b: |- B = ( Base ` K )
  assume dihjatcclem.l: |- .<_ = ( le ` K )
  assume dihjatcclem.h: |- H = ( LHyp ` K )
  assume dihjatcclem.j: |- .\/ = ( join ` K )
  assume dihjatcclem.m: |- ./\ = ( meet ` K )
  assume dihjatcclem.a: |- A = ( Atoms ` K )
  assume dihjatcclem.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjatcclem.s: |- .(+) = ( LSSum ` U )
  assume dihjatcclem.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihjatcclem.v: |- V = ( ( P .\/ Q ) ./\ W )
  assume dihjatcclem.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihjatcclem.p: |- ( ph -> ( P e. A /\ -. P .<_ W ) )
  assume dihjatcclem.q: |- ( ph -> ( Q e. A /\ -. Q .<_ W ) )
  assume dihjatcc.w: |- C = ( ( oc ` K ) ` W )
  assume dihjatcc.t: |- T = ( ( LTrn ` K ) ` W )
  assume dihjatcc.r: |- R = ( ( trL ` K ) ` W )
  assume dihjatcc.e: |- E = ( ( TEndo ` K ) ` W )
  assume dihjatcc.g: |- G = ( iota_ d e. T ( d ` C ) = P )
  assume dihjatcc.dd: |- D = ( iota_ d e. T ( d ` C ) = Q )
  assume dihjatcc.n: |- N = ( a e. E |-> ( d e. T |-> `' ( a ` d ) ) )
  assume dihjatcc.o: |- .0. = ( d e. T |-> ( _I |` B ) )
  assume dihjatcc.d: |- J = ( a e. E , b e. E |-> ( d e. T |-> ( ( a ` d ) o. ( b ` d ) ) ) )

  disjoint .<_ d
  disjoint A d
  disjoint B d
  disjoint C d
  disjoint a b
  disjoint E a
  disjoint E b
  disjoint H d
  disjoint P d
  disjoint a d
  disjoint K a
  disjoint b d
  disjoint K b
  disjoint K d
  disjoint Q d
  disjoint T a
  disjoint T b
  disjoint T d
  disjoint W a
  disjoint W b
  disjoint W d
  disjoint d t
  disjoint .<_ t
  disjoint f s
  disjoint .(+) f
  disjoint .(+) s
  disjoint .0. t
  disjoint g h
  disjoint g t
  disjoint g u
  disjoint D g
  disjoint h t
  disjoint h u
  disjoint D h
  disjoint t u
  disjoint D t
  disjoint D u
  disjoint a t
  disjoint b t
  disjoint E t
  disjoint d g
  disjoint H g
  disjoint H t
  disjoint J g
  disjoint J h
  disjoint J u
  disjoint N g
  disjoint N h
  disjoint N u
  disjoint f g
  disjoint f h
  disjoint f t
  disjoint f u
  disjoint I f
  disjoint g s
  disjoint I g
  disjoint h s
  disjoint I h
  disjoint s t
  disjoint s u
  disjoint I s
  disjoint I t
  disjoint I u
  disjoint d f
  disjoint d h
  disjoint d s
  disjoint d u
  disjoint P f
  disjoint P g
  disjoint P h
  disjoint P s
  disjoint P t
  disjoint P u
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint R t
  disjoint G g
  disjoint G h
  disjoint G t
  disjoint G u
  disjoint a g
  disjoint b g
  disjoint K g
  disjoint K t
  disjoint Q f
  disjoint Q g
  disjoint Q h
  disjoint Q s
  disjoint Q t
  disjoint Q u
  disjoint T t
  disjoint U g
  disjoint U h
  disjoint U t
  disjoint U u
  disjoint V f
  disjoint V s
  disjoint V t
  disjoint W g
  disjoint W t
  assert |- ( ph -> ( I ` V ) C_ ( ( I ` P ) .(+) ( I ` Q ) ) )

  proof
    wph
    vf
    vs
    cV
    cI
    cfv
    #
    cP
    cI
    cfv
    #
    cQ
    cI
    cfv
    #
    c.po
    co
    #
    wph
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    @0
    wrel
    dihjatcclem.k
    cH
    cI
    cK
    cW
    cV
    dihjatcclem.h
    dihjatcclem.i
    dihvalrel
    syl
    wph
    vf
    cv
    #
    cT
    wcel
    #
    @7
    cR
    cfv
    #
    cV
    c.le
    wbr
    #
    wa
    #
    vs
    cv
    #
    c.0
    wceq
    #
    wa
    #
    vg
    cv
    #
    vt
    cv
    #
    cop
    #
    @1
    wcel
    #
    vh
    cv
    #
    vu
    cv
    #
    cop
    #
    @2
    wcel
    #
    wa
    #
    @7
    @15
    @19
    ccom
    #
    wceq
    #
    @12
    @16
    @20
    cJ
    co
    #
    wceq
    #
    wa
    #
    wa
    #
    vu
    wex
    vh
    wex
    #
    vt
    wex
    vg
    wex
    #
    @7
    @12
    cop
    #
    @0
    wcel
    #
    @32
    @3
    wcel
    wph
    @14
    @31
    wph
    @14
    wa
    #
    @16
    cE
    wcel
    #
    cG
    cD
    ccnv
    #
    ccom
    #
    @16
    cfv
    #
    @7
    wceq
    #
    wa
    #
    vt
    wex
    #
    @31
    @34
    @39
    vt
    cE
    wrex
    #
    @41
    @34
    @6
    @37
    cT
    wcel
    #
    @8
    @9
    @37
    cR
    cfv
    #
    c.le
    wbr
    @42
    wph
    @6
    @14
    dihjatcclem.k
    adantr
    wph
    @43
    @14
    wph
    @6
    cG
    cT
    wcel
    #
    @36
    cT
    wcel
    #
    @43
    dihjatcclem.k
    wph
    @6
    cC
    cA
    wcel
    cC
    cW
    c.le
    wbr
    wn
    wa
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    @45
    dihjatcclem.k
    wph
    @6
    @47
    dihjatcclem.k
    cA
    cC
    cH
    cK
    c.le
    cW
    dihjatcclem.l
    dihjatcclem.a
    dihjatcclem.h
    dihjatcc.w
    lhpocnel2
    syl
    #
    dihjatcclem.p
    cA
    cC
    cP
    cT
    vd
    cG
    cH
    cK
    c.le
    cW
    dihjatcclem.l
    dihjatcclem.a
    dihjatcclem.h
    dihjatcc.t
    dihjatcc.g
    ltrniotacl
    syl3anc
    #
    wph
    @6
    cD
    cT
    wcel
    #
    @46
    dihjatcclem.k
    wph
    @6
    @47
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    @53
    dihjatcclem.k
    @51
    dihjatcclem.q
    cA
    cC
    cQ
    cT
    vd
    cD
    cH
    cK
    c.le
    cW
    dihjatcclem.l
    dihjatcclem.a
    dihjatcclem.h
    dihjatcc.t
    dihjatcc.dd
    ltrniotacl
    syl3anc
    #
    cT
    cD
    cH
    cK
    cW
    dihjatcclem.h
    dihjatcc.t
    ltrncnv
    syl2anc
    #
    cT
    cG
    @36
    cH
    cK
    cW
    dihjatcclem.h
    dihjatcc.t
    ltrnco
    syl3anc
    adantr
    wph
    @8
    @10
    @13
    simprll
    @34
    @9
    cV
    @44
    c.le
    wph
    @8
    @10
    @13
    simprlr
    wph
    @44
    cV
    wceq
    @14
    wph
    cA
    cB
    cC
    cD
    cP
    c.po
    cQ
    cR
    cT
    cU
    cE
    cG
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cV
    cW
    vd
    dihjatcclem.b
    dihjatcclem.l
    dihjatcclem.h
    dihjatcclem.j
    dihjatcclem.m
    dihjatcclem.a
    dihjatcclem.u
    dihjatcclem.s
    dihjatcclem.i
    dihjatcclem.v
    dihjatcclem.k
    dihjatcclem.p
    dihjatcclem.q
    dihjatcc.w
    dihjatcc.t
    dihjatcc.r
    dihjatcc.e
    dihjatcc.g
    dihjatcc.dd
    dihjatcclem3
    adantr
    breqtrrd
    vt
    cR
    cT
    cE
    @37
    cH
    cK
    c.le
    @7
    cW
    dihjatcclem.l
    dihjatcclem.h
    dihjatcc.t
    dihjatcc.r
    dihjatcc.e
    tendoex
    syl121anc
    @39
    vt
    cE
    df-rex
    sylib
    @34
    @41
    @30
    vg
    wex
    #
    vt
    wex
    @31
    @34
    @40
    @59
    vt
    @34
    @40
    @59
    @34
    @40
    wa
    #
    cG
    @16
    cfv
    #
    @16
    cop
    #
    @1
    wcel
    #
    cD
    @16
    cN
    cfv
    #
    cfv
    #
    @64
    cop
    #
    @2
    wcel
    #
    @7
    @61
    @65
    ccom
    #
    wceq
    #
    @12
    @16
    @64
    cJ
    co
    #
    wceq
    #
    @59
    @60
    @63
    @61
    @61
    wceq
    #
    @35
    @60
    @61
    eqidd
    @34
    @35
    @39
    simprl
    #
    @60
    @6
    @50
    @63
    @72
    @35
    wa
    wb
    wph
    @6
    @14
    @40
    dihjatcclem.k
    ad2antrr
    #
    wph
    @50
    @14
    @40
    dihjatcclem.p
    ad2antrr
    cA
    cC
    cP
    @16
    cT
    vd
    cE
    @61
    cG
    cH
    cI
    cK
    c.le
    cW
    dihjatcclem.l
    dihjatcclem.a
    dihjatcclem.h
    dihjatcc.w
    dihjatcc.t
    dihjatcc.e
    dihjatcclem.i
    dihjatcc.g
    cG
    @16
    fvex
    #
    vt
    vex
    dihopelvalcqat
    syl2anc
    mpbir2and
    @60
    @67
    @65
    @65
    wceq
    #
    @64
    cE
    wcel
    #
    @60
    @65
    eqidd
    @60
    @6
    @35
    @77
    @74
    @73
    @16
    cT
    vd
    cE
    cH
    cN
    cK
    cW
    va
    dihjatcclem.h
    dihjatcc.t
    dihjatcc.e
    dihjatcc.n
    tendoicl
    syl2anc
    @60
    @6
    @56
    @67
    @76
    @77
    wa
    wb
    @74
    wph
    @56
    @14
    @40
    dihjatcclem.q
    ad2antrr
    cA
    cC
    cQ
    @64
    cT
    vd
    cE
    @65
    cD
    cH
    cI
    cK
    c.le
    cW
    dihjatcclem.l
    dihjatcclem.a
    dihjatcclem.h
    dihjatcc.w
    dihjatcc.t
    dihjatcc.e
    dihjatcclem.i
    dihjatcc.dd
    cD
    @64
    fvex
    #
    @16
    cN
    fvex
    #
    dihopelvalcqat
    syl2anc
    mpbir2and
    @60
    @38
    @61
    @36
    @16
    cfv
    #
    ccom
    #
    @7
    @68
    @60
    @6
    @35
    @45
    @46
    @38
    @81
    wceq
    @74
    @73
    wph
    @45
    @14
    @40
    @52
    ad2antrr
    wph
    @46
    @14
    @40
    @58
    ad2antrr
    cT
    @16
    cE
    cG
    @36
    cH
    cK
    chlt
    cW
    dihjatcclem.h
    dihjatcc.t
    dihjatcc.e
    tendospdi1
    syl13anc
    @34
    @35
    @39
    simprr
    @60
    @80
    @65
    @61
    @60
    @65
    cD
    @16
    cfv
    ccnv
    #
    @80
    @60
    @35
    @53
    @65
    @82
    wceq
    @73
    wph
    @53
    @14
    @40
    @57
    ad2antrr
    #
    @16
    cT
    vd
    cE
    cD
    cN
    cK
    cW
    va
    dihjatcc.n
    dihjatcc.t
    tendoi2
    syl2anc
    @60
    @6
    @35
    @53
    @82
    @80
    wceq
    @74
    @73
    @83
    @16
    cT
    cE
    cD
    cH
    cK
    cW
    dihjatcclem.h
    dihjatcc.t
    dihjatcc.e
    tendocnv
    syl3anc
    eqtr2d
    coeq2d
    3eqtr3d
    @60
    @12
    c.0
    @70
    wph
    @11
    @13
    @40
    simplrr
    @60
    @6
    @35
    @70
    c.0
    wceq
    @74
    @73
    vb
    cB
    cJ
    @16
    cT
    vd
    cE
    cH
    cN
    cK
    c.0
    cW
    va
    dihjatcclem.h
    dihjatcc.t
    dihjatcc.e
    dihjatcc.n
    dihjatcclem.b
    dihjatcc.d
    dihjatcc.o
    tendoipl2
    syl2anc
    eqtr4d
    @61
    cvv
    wcel
    @65
    cvv
    wcel
    @64
    cvv
    wcel
    @63
    @67
    wa
    #
    @69
    @71
    wa
    #
    wa
    #
    @59
    wi
    @75
    @78
    @79
    @29
    @86
    vg
    vh
    vu
    @61
    @65
    @64
    cvv
    cvv
    cvv
    @15
    @61
    wceq
    #
    @29
    @63
    @22
    wa
    #
    @7
    @61
    @19
    ccom
    #
    wceq
    #
    @27
    wa
    #
    wa
    @19
    @65
    wceq
    #
    @63
    @65
    @20
    cop
    #
    @2
    wcel
    #
    wa
    #
    @69
    @27
    wa
    #
    wa
    @20
    @64
    wceq
    #
    @86
    @87
    @23
    @88
    @28
    @91
    @87
    @18
    @63
    @22
    @87
    @17
    @62
    @1
    @15
    @61
    @16
    opeq1
    eleq1d
    anbi1d
    @87
    @25
    @90
    @27
    @87
    @24
    @89
    @7
    @15
    @61
    @19
    coeq1
    eqeq2d
    anbi1d
    anbi12d
    @92
    @88
    @95
    @91
    @96
    @92
    @22
    @94
    @63
    @92
    @21
    @93
    @2
    @19
    @65
    @20
    opeq1
    eleq1d
    anbi2d
    @92
    @90
    @69
    @27
    @92
    @89
    @68
    @7
    @19
    @65
    @61
    coeq2
    eqeq2d
    anbi1d
    anbi12d
    @97
    @95
    @84
    @96
    @85
    @97
    @94
    @67
    @63
    @97
    @93
    @66
    @2
    @20
    @64
    @65
    opeq2
    eleq1d
    anbi2d
    @97
    @27
    @71
    @69
    @97
    @26
    @70
    @12
    @20
    @64
    @16
    cJ
    oveq2
    eqeq2d
    anbi2d
    anbi12d
    syl3an9b
    spc3egv
    mp3an
    syl22anc
    ex
    eximdv
    @30
    vt
    vg
    excom
    syl6ib
    mpd
    ex
    wph
    @33
    @32
    cV
    cW
    cK
    cdib
    cfv
    cfv
    #
    cfv
    #
    wcel
    #
    @14
    wph
    @0
    @99
    @32
    wph
    @6
    cV
    cB
    wcel
    #
    cV
    cW
    c.le
    wbr
    #
    @0
    @99
    wceq
    dihjatcclem.k
    wph
    cV
    cP
    cQ
    c.or
    co
    #
    cW
    c.an
    co
    #
    cB
    dihjatcclem.v
    wph
    cK
    clat
    wcel
    #
    @103
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @104
    cB
    wcel
    wph
    @4
    @105
    wph
    @4
    @5
    dihjatcclem.k
    simpld
    #
    cK
    hllat
    syl
    #
    wph
    @4
    @48
    @54
    @106
    @108
    wph
    @48
    @49
    dihjatcclem.p
    simpld
    #
    wph
    @54
    @55
    dihjatcclem.q
    simpld
    #
    cA
    cB
    c.or
    cK
    cP
    cQ
    dihjatcclem.b
    dihjatcclem.j
    dihjatcclem.a
    hlatjcl
    syl3anc
    #
    wph
    @5
    @107
    wph
    @4
    @5
    dihjatcclem.k
    simprd
    cB
    cH
    cK
    cW
    dihjatcclem.b
    dihjatcclem.h
    lhpbase
    syl
    #
    cB
    cK
    c.an
    @103
    cW
    dihjatcclem.b
    dihjatcclem.m
    latmcl
    syl3anc
    syl5eqel
    #
    wph
    cV
    @104
    cW
    c.le
    dihjatcclem.v
    wph
    @105
    @106
    @107
    @104
    cW
    c.le
    wbr
    @109
    @112
    @113
    cB
    cK
    c.le
    c.an
    @103
    cW
    dihjatcclem.b
    dihjatcclem.l
    dihjatcclem.m
    latmle2
    syl3anc
    syl5eqbr
    #
    cB
    @98
    cH
    cI
    cK
    c.le
    chlt
    cW
    cV
    dihjatcclem.b
    dihjatcclem.l
    dihjatcclem.h
    dihjatcclem.i
    @98
    eqid
    #
    dihvalb
    syl12anc
    eleq2d
    wph
    @6
    @101
    @102
    @100
    @14
    wb
    dihjatcclem.k
    @114
    @115
    cB
    cR
    @12
    cT
    vd
    @7
    cH
    @98
    cK
    c.le
    chlt
    cW
    cV
    c.0
    dihjatcclem.b
    dihjatcclem.l
    dihjatcclem.h
    dihjatcc.t
    dihjatcc.r
    dihjatcc.o
    @116
    dibopelval3
    syl12anc
    bitrd
    wph
    vb
    va
    vu
    vt
    cJ
    cB
    c.po
    @12
    cT
    cU
    vg
    vh
    vd
    cE
    @7
    cH
    cI
    cK
    cU
    clss
    cfv
    #
    cW
    cP
    cQ
    dihjatcclem.b
    dihjatcclem.h
    dihjatcc.t
    dihjatcc.e
    dihjatcc.d
    dihjatcclem.u
    @117
    eqid
    dihjatcclem.s
    dihjatcclem.i
    dihjatcclem.k
    wph
    @48
    cP
    cB
    wcel
    @110
    cA
    cB
    cP
    cK
    dihjatcclem.b
    dihjatcclem.a
    atbase
    syl
    wph
    @54
    cQ
    cB
    wcel
    @111
    cA
    cB
    cQ
    cK
    dihjatcclem.b
    dihjatcclem.a
    atbase
    syl
    dihopellsm
    3imtr4d
    relssdv
end
