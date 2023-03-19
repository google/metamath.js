include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "cdif.mm"
include "wrex.mm"
include "crn.mm"
include "clvec.mm"
include "wb.mm"
include "id.mm"
include "dvhlvec.mm"
include "islsat.mm"
include "syl.mm"
include "biimpa.mm"
include "wi.mm"
include "cxp.mm"
include "eldifi.mm"
include "dvhvbase.mm"
include "eleq2d.mm"
include "syl5ib.mm"
include "imp.mm"
include "cop.mm"
include "wral.mm"
include "simpr.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "cdib.mm"
include "wbr.mm"
include "simpl.mm"
include "trlcl.mm"
include "trlle.mm"
include "eqid.mm"
include "dihvalb.mm"
include "syl12anc.mm"
include "dib1dim2.mm"
include "eqtr2d.mm"
include "wfn.mm"
include "wf1.mm"
include "dihf11.mm"
include "adantr.mm"
include "f1fn.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "adantrr.mm"
include "wne.mm"
include "co.mm"
include "cbs.mm"
include "cab.mm"
include "copab.mm"
include "ccom.mm"
include "crab.mm"
include "simpll.mm"
include "dvhbase.mm"
include "rexeqdv.mm"
include "simplll.mm"
include "opelxpi.mm"
include "ad3antlr.mm"
include "dvhvscacl.mm"
include "eleq1a.mm"
include "rexlimdva.mm"
include "pm4.71rd.mm"
include "simplrl.mm"
include "simplrr.mm"
include "dvhopvsca.mm"
include "syl13anc.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "anbi2d.mm"
include "3bitrd.mm"
include "abbidv.mm"
include "df-rab.mm"
include "syl6eqr.mm"
include "wss.mm"
include "wrel.mm"
include "ssrab2.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"
include "relopab.mm"
include "vex.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "fveq1.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "opelopab.mm"
include "dih1dimatlem0.mm"
include "3expa.mm"
include "opelxp.mm"
include "opth.mm"
include "rexbii.mm"
include "anbi12i.mm"
include "syl6bbr.mm"
include "rexbidv.mm"
include "elrab.mm"
include "syl5rbb.mm"
include "eqrelrdv.mm"
include "eqtrd.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "dvhelvbasei.mm"
include "lspsn.mm"
include "cdic.mm"
include "wn.mm"
include "w3a.mm"
include "tendoinvcl.mm"
include "simpld.mm"
include "syl3anc.mm"
include "tendocl.mm"
include "lhpocnel2.mm"
include "ltrnel.mm"
include "dihvalcqat.mm"
include "dicval2.mm"
include "3eqtr4d.mm"
include "dihfn.mm"
include "coc.mm"
include "cops.mm"
include "hlop.mm"
include "lhpbase.mm"
include "opoccl.mm"
include "syl5eqel.mm"
include "ltrncl.mm"
include "pm2.61dane.mm"
include "ralrimivva.mm"
include "sneq.mm"
include "eleq1d.mm"
include "ralxp.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "syldan.mm"
include "mpd.mm"

theorem dih1dimatlem
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vs: setvar s
  let vv: setvar v
  let vg: setvar g
  let vi: setvar i
  let vp: setvar p
  let vr: setvar r
  let vt: setvar t
  let vu: setvar u
  assume dih1dimat.h: |- H = ( LHyp ` K )
  assume dih1dimat.u: |- U = ( ( DVecH ` K ) ` W )
  assume dih1dimat.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dih1dimat.a: |- A = ( LSAtoms ` U )
  assume dih1dimat.b: |- B = ( Base ` K )
  assume dih1dimat.l: |- .<_ = ( le ` K )
  assume dih1dimat.c: |- C = ( Atoms ` K )
  assume dih1dimat.p: |- P = ( ( oc ` K ) ` W )
  assume dih1dimat.t: |- T = ( ( LTrn ` K ) ` W )
  assume dih1dimat.r: |- R = ( ( trL ` K ) ` W )
  assume dih1dimat.e: |- E = ( ( TEndo ` K ) ` W )
  assume dih1dimat.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume dih1dimat.d: |- F = ( Scalar ` U )
  assume dih1dimat.j: |- J = ( invr ` F )
  assume dih1dimat.v: |- V = ( Base ` U )
  assume dih1dimat.m: |- .x. = ( .s ` U )
  assume dih1dimat.s: |- S = ( LSubSp ` U )
  assume dih1dimat.n: |- N = ( LSpan ` U )
  assume dih1dimat.z: |- .0. = ( 0g ` U )
  assume dih1dimat.g: |- G = ( iota_ h e. T ( h ` P ) = ( ( ( J ` s ) ` f ) ` P ) )

  disjoint .<_ h
  disjoint B h
  disjoint f s
  disjoint E f
  disjoint E s
  disjoint C h
  disjoint J h
  disjoint N f
  disjoint N s
  disjoint f h
  disjoint K f
  disjoint h s
  disjoint K h
  disjoint K s
  disjoint T f
  disjoint T h
  disjoint T s
  disjoint U f
  disjoint U h
  disjoint U s
  disjoint H f
  disjoint H h
  disjoint H s
  disjoint V f
  disjoint V s
  disjoint W f
  disjoint W h
  disjoint W s
  disjoint I f
  disjoint I s
  disjoint P h
  disjoint .0. v
  disjoint f g
  disjoint f i
  disjoint f p
  disjoint f r
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint g i
  disjoint g p
  disjoint g r
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint E g
  disjoint i p
  disjoint i r
  disjoint i s
  disjoint i t
  disjoint i u
  disjoint i v
  disjoint E i
  disjoint p r
  disjoint p s
  disjoint p t
  disjoint p u
  disjoint p v
  disjoint E p
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint E r
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint t u
  disjoint t v
  disjoint E t
  disjoint u v
  disjoint E u
  disjoint E v
  disjoint F t
  disjoint F u
  disjoint D v
  disjoint G g
  disjoint G i
  disjoint G p
  disjoint G r
  disjoint G t
  disjoint g h
  disjoint J g
  disjoint h r
  disjoint h t
  disjoint J r
  disjoint J t
  disjoint N t
  disjoint N u
  disjoint N v
  disjoint K g
  disjoint h i
  disjoint h p
  disjoint h u
  disjoint h v
  disjoint K i
  disjoint K p
  disjoint K r
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint T g
  disjoint T i
  disjoint T p
  disjoint T t
  disjoint T u
  disjoint T v
  disjoint U t
  disjoint U u
  disjoint U v
  disjoint H i
  disjoint H p
  disjoint H t
  disjoint H u
  disjoint H v
  disjoint V i
  disjoint V p
  disjoint V t
  disjoint V u
  disjoint V v
  disjoint W g
  disjoint W i
  disjoint W p
  disjoint W r
  disjoint W t
  disjoint W u
  disjoint W v
  disjoint I v
  disjoint O i
  disjoint O p
  disjoint O t
  disjoint O u
  disjoint P g
  disjoint P r
  disjoint .x. t
  disjoint .x. u
  assert |- ( ( ( K e. HL /\ W e. H ) /\ D e. A ) -> D e. ran I )

  proof
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
    cD
    cA
    wcel
    #
    wa
    cD
    vv
    cv
    #
    csn
    #
    cN
    cfv
    #
    wceq
    #
    vv
    cV
    c.0
    csn
    #
    cdif
    #
    wrex
    #
    cD
    cI
    crn
    #
    wcel
    #
    @2
    @3
    @10
    @2
    cU
    clvec
    wcel
    @3
    @10
    wb
    @2
    cU
    cH
    cK
    cW
    dih1dimat.h
    dih1dimat.u
    @2
    id
    dvhlvec
    vv
    cA
    cD
    cN
    cV
    cU
    clvec
    c.0
    dih1dimat.v
    dih1dimat.n
    dih1dimat.z
    dih1dimat.a
    islsat
    syl
    biimpa
    @2
    @10
    @12
    wi
    @3
    @2
    @7
    @12
    vv
    @9
    @2
    @4
    @9
    wcel
    #
    wa
    @6
    @11
    wcel
    #
    @7
    @12
    wi
    @2
    @13
    @4
    cT
    cE
    cxp
    #
    wcel
    #
    @14
    @2
    @13
    @16
    @13
    @4
    cV
    wcel
    @2
    @16
    @4
    cV
    @8
    eldifi
    @2
    cV
    @15
    @4
    cT
    cU
    cE
    cH
    cK
    cV
    cW
    chlt
    dih1dimat.h
    dih1dimat.t
    dih1dimat.e
    dih1dimat.u
    dih1dimat.v
    dvhvbase
    eleq2d
    syl5ib
    imp
    @2
    @14
    vv
    @15
    @2
    vf
    cv
    #
    vs
    cv
    #
    cop
    #
    csn
    #
    cN
    cfv
    #
    @11
    wcel
    #
    vs
    cE
    wral
    vf
    cT
    wral
    @14
    vv
    @15
    wral
    @2
    @22
    vf
    vs
    cT
    cE
    @2
    @17
    cT
    wcel
    #
    @18
    cE
    wcel
    #
    wa
    #
    wa
    #
    @22
    @18
    cO
    @26
    @18
    cO
    wceq
    #
    wa
    #
    @21
    @17
    cO
    cop
    #
    csn
    #
    cN
    cfv
    #
    @11
    @28
    @20
    @30
    cN
    @28
    @19
    @29
    @28
    @18
    cO
    @17
    @26
    @27
    simpr
    opeq2d
    sneqd
    fveq2d
    @26
    @31
    @11
    wcel
    #
    @27
    @2
    @23
    @32
    @24
    @2
    @23
    wa
    #
    @31
    @17
    cR
    cfv
    #
    cI
    cfv
    #
    @11
    @33
    @35
    @34
    cW
    cK
    cdib
    cfv
    cfv
    #
    cfv
    #
    @31
    @33
    @2
    @34
    cB
    wcel
    #
    @34
    cW
    c.le
    wbr
    @35
    @37
    wceq
    @2
    @23
    simpl
    cB
    cR
    cT
    @17
    cH
    cK
    cW
    dih1dimat.b
    dih1dimat.h
    dih1dimat.t
    dih1dimat.r
    trlcl
    #
    cR
    cT
    @17
    cH
    cK
    c.le
    cW
    dih1dimat.l
    dih1dimat.h
    dih1dimat.t
    dih1dimat.r
    trlle
    cB
    @36
    cH
    cI
    cK
    c.le
    chlt
    cW
    @34
    dih1dimat.b
    dih1dimat.l
    dih1dimat.h
    dih1dimat.i
    @36
    eqid
    #
    dihvalb
    syl12anc
    cB
    cR
    cT
    cU
    vh
    @17
    cH
    @36
    cK
    cN
    cO
    cW
    dih1dimat.b
    dih1dimat.h
    dih1dimat.t
    dih1dimat.r
    dih1dimat.o
    dih1dimat.u
    @40
    dih1dimat.n
    dib1dim2
    eqtr2d
    @33
    cI
    cB
    wfn
    #
    @38
    @35
    @11
    wcel
    @33
    cB
    cS
    cI
    wf1
    #
    @41
    @2
    @42
    @23
    cB
    cS
    cU
    cH
    cI
    cK
    cW
    dih1dimat.b
    dih1dimat.h
    dih1dimat.i
    dih1dimat.u
    dih1dimat.s
    dihf11
    adantr
    cB
    cS
    cI
    f1fn
    syl
    @39
    cB
    @34
    cI
    fnfvelrn
    syl2anc
    eqeltrd
    adantrr
    adantr
    eqeltrd
    @26
    @18
    cO
    wne
    #
    wa
    #
    @21
    cP
    @17
    @18
    cJ
    cfv
    #
    cfv
    #
    cfv
    #
    cI
    cfv
    #
    @11
    @44
    vu
    cv
    #
    vt
    cv
    #
    @19
    c.x
    co
    #
    wceq
    #
    vt
    cF
    cbs
    cfv
    #
    wrex
    #
    vu
    cab
    #
    vg
    cv
    #
    cG
    vr
    cv
    #
    cfv
    #
    wceq
    #
    @57
    cE
    wcel
    #
    wa
    #
    vg
    vr
    copab
    #
    @21
    @48
    @44
    @55
    @49
    @17
    @50
    cfv
    #
    @50
    @18
    ccom
    #
    cop
    #
    wceq
    #
    vt
    cE
    wrex
    #
    vu
    @15
    crab
    #
    @62
    @44
    @55
    @49
    @15
    wcel
    #
    @67
    wa
    #
    vu
    cab
    @68
    @44
    @54
    @70
    vu
    @44
    @54
    @52
    vt
    cE
    wrex
    #
    @69
    @71
    wa
    @70
    @44
    @52
    vt
    @53
    cE
    @44
    @2
    @53
    cE
    wceq
    @2
    @25
    @43
    simpll
    #
    @53
    cU
    cE
    cF
    cH
    cK
    cW
    chlt
    dih1dimat.h
    dih1dimat.e
    dih1dimat.u
    dih1dimat.d
    @53
    eqid
    #
    dvhbase
    syl
    rexeqdv
    @44
    @71
    @69
    @44
    @52
    @69
    vt
    cE
    @44
    @50
    cE
    wcel
    #
    wa
    #
    @51
    @15
    wcel
    #
    @52
    @69
    wi
    @75
    @2
    @74
    @19
    @15
    wcel
    #
    @76
    @2
    @25
    @43
    @74
    simplll
    #
    @44
    @74
    simpr
    #
    @25
    @77
    @2
    @43
    @74
    @17
    @18
    cT
    cE
    opelxpi
    ad3antlr
    @50
    cT
    c.x
    cU
    cE
    @19
    cH
    cK
    cW
    dih1dimat.h
    dih1dimat.t
    dih1dimat.e
    dih1dimat.u
    dih1dimat.m
    dvhvscacl
    syl12anc
    @51
    @15
    @49
    eleq1a
    syl
    rexlimdva
    pm4.71rd
    @44
    @71
    @67
    @69
    @44
    @52
    @66
    vt
    cE
    @75
    @51
    @65
    @49
    @75
    @2
    @74
    @23
    @24
    @51
    @65
    wceq
    @78
    @79
    @44
    @23
    @74
    @2
    @23
    @24
    @43
    simplrl
    #
    adantr
    @44
    @24
    @74
    @2
    @23
    @24
    @43
    simplrr
    #
    adantr
    @50
    cT
    c.x
    cU
    cE
    @17
    cH
    cK
    chlt
    cW
    @18
    dih1dimat.h
    dih1dimat.t
    dih1dimat.e
    dih1dimat.u
    dih1dimat.m
    dvhopvsca
    syl13anc
    eqeq2d
    rexbidva
    anbi2d
    3bitrd
    abbidv
    @67
    vu
    @15
    df-rab
    syl6eqr
    @44
    vi
    vp
    @68
    @62
    @68
    @15
    wss
    @15
    wrel
    @68
    wrel
    @67
    vu
    @15
    ssrab2
    cT
    cE
    relxp
    @68
    @15
    relss
    mp2
    @61
    vg
    vr
    relopab
    vi
    cv
    #
    vp
    cv
    #
    cop
    #
    @62
    wcel
    @82
    cG
    @83
    cfv
    #
    wceq
    #
    @83
    cE
    wcel
    #
    wa
    #
    @44
    @84
    @68
    wcel
    #
    @61
    @82
    @58
    wceq
    #
    @60
    wa
    @88
    vg
    vr
    @82
    @83
    vi
    vex
    #
    vp
    vex
    #
    @56
    @82
    wceq
    @59
    @90
    @60
    @56
    @82
    @58
    eqeq1
    anbi1d
    @57
    @83
    wceq
    #
    @90
    @86
    @60
    @87
    @93
    @58
    @85
    @82
    cG
    @57
    @83
    fveq1
    eqeq2d
    @57
    @83
    cE
    eleq1
    anbi12d
    opelopab
    @44
    @88
    @84
    @15
    wcel
    #
    @84
    @65
    wceq
    #
    vt
    cE
    wrex
    #
    wa
    #
    @89
    @44
    @88
    @82
    cT
    wcel
    @87
    wa
    #
    @82
    @63
    wceq
    @83
    @64
    wceq
    wa
    #
    vt
    cE
    wrex
    #
    wa
    #
    @97
    @2
    @25
    @43
    @88
    @101
    wb
    vt
    cA
    cB
    cC
    cP
    cR
    cS
    cT
    c.x
    cU
    vf
    vh
    vi
    cE
    cF
    cG
    cH
    cI
    cJ
    cK
    c.le
    cN
    cO
    cV
    cW
    c.0
    vs
    vp
    dih1dimat.h
    dih1dimat.u
    dih1dimat.i
    dih1dimat.a
    dih1dimat.b
    dih1dimat.l
    dih1dimat.c
    dih1dimat.p
    dih1dimat.t
    dih1dimat.r
    dih1dimat.e
    dih1dimat.o
    dih1dimat.d
    dih1dimat.j
    dih1dimat.v
    dih1dimat.m
    dih1dimat.s
    dih1dimat.n
    dih1dimat.z
    dih1dimat.g
    dih1dimatlem0
    3expa
    @94
    @98
    @96
    @100
    @82
    @83
    cT
    cE
    opelxp
    @95
    @99
    vt
    cE
    @82
    @83
    @63
    @64
    @91
    @92
    opth
    rexbii
    anbi12i
    syl6bbr
    @67
    @96
    vu
    @84
    @15
    @49
    @84
    wceq
    @66
    @95
    vt
    cE
    @49
    @84
    @65
    eqeq1
    rexbidv
    elrab
    syl6bbr
    syl5rbb
    eqrelrdv
    eqtrd
    @44
    cU
    clmod
    wcel
    @19
    cV
    wcel
    #
    @21
    @55
    wceq
    @44
    cU
    cH
    cK
    cW
    dih1dimat.h
    dih1dimat.u
    @72
    dvhlmod
    @26
    @102
    @43
    @18
    cT
    cU
    cE
    @17
    cH
    cK
    cV
    cW
    chlt
    dih1dimat.h
    dih1dimat.t
    dih1dimat.e
    dih1dimat.u
    dih1dimat.v
    dvhelvbasei
    adantr
    vu
    c.x
    vt
    cF
    @53
    cN
    cV
    cU
    @19
    dih1dimat.d
    @73
    dih1dimat.v
    dih1dimat.m
    dih1dimat.n
    lspsn
    syl2anc
    @44
    @48
    @47
    cW
    cK
    cdic
    cfv
    cfv
    #
    cfv
    #
    @62
    @44
    @2
    @47
    cC
    wcel
    @47
    cW
    c.le
    wbr
    wn
    wa
    #
    @48
    @104
    wceq
    @72
    @44
    @2
    @46
    cT
    wcel
    #
    cP
    cC
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    @105
    @72
    @44
    @2
    @45
    cE
    wcel
    #
    @23
    @106
    @72
    @44
    @2
    @24
    @43
    @108
    @72
    @81
    @26
    @43
    simpr
    @2
    @24
    @43
    w3a
    @108
    @45
    cO
    wne
    cB
    @18
    cT
    cU
    vh
    cE
    cF
    cH
    cK
    cJ
    cO
    cW
    dih1dimat.b
    dih1dimat.h
    dih1dimat.t
    dih1dimat.e
    dih1dimat.o
    dih1dimat.u
    dih1dimat.d
    dih1dimat.j
    tendoinvcl
    simpld
    syl3anc
    @80
    @45
    cT
    cE
    @17
    cH
    cK
    chlt
    cW
    dih1dimat.h
    dih1dimat.t
    dih1dimat.e
    tendocl
    syl3anc
    #
    @44
    @2
    @107
    @72
    cC
    cP
    cH
    cK
    c.le
    cW
    dih1dimat.l
    dih1dimat.c
    dih1dimat.h
    dih1dimat.p
    lhpocnel2
    syl
    cC
    cP
    cT
    @46
    cH
    cK
    c.le
    cW
    dih1dimat.l
    dih1dimat.c
    dih1dimat.h
    dih1dimat.t
    ltrnel
    syl3anc
    #
    cC
    @47
    cH
    cI
    @103
    cK
    c.le
    cW
    dih1dimat.l
    dih1dimat.c
    dih1dimat.h
    @103
    eqid
    #
    dih1dimat.i
    dihvalcqat
    syl2anc
    @44
    @2
    @105
    @104
    @62
    wceq
    @72
    @110
    cC
    cP
    @47
    cT
    vg
    vh
    cE
    cG
    cH
    @103
    cK
    c.le
    chlt
    cW
    vr
    dih1dimat.l
    dih1dimat.c
    dih1dimat.h
    dih1dimat.p
    dih1dimat.t
    dih1dimat.e
    @111
    dih1dimat.g
    dicval2
    syl2anc
    eqtrd
    3eqtr4d
    @44
    @41
    @47
    cB
    wcel
    #
    @48
    @11
    wcel
    @26
    @41
    @43
    @2
    @41
    @25
    cB
    cH
    cI
    cK
    cW
    dih1dimat.b
    dih1dimat.h
    dih1dimat.i
    dihfn
    adantr
    adantr
    @44
    @2
    @106
    cP
    cB
    wcel
    @112
    @72
    @109
    @44
    cP
    cW
    cK
    coc
    cfv
    #
    cfv
    #
    cB
    dih1dimat.p
    @44
    cK
    cops
    wcel
    #
    cW
    cB
    wcel
    #
    @114
    cB
    wcel
    @44
    @0
    @115
    @0
    @1
    @25
    @43
    simplll
    cK
    hlop
    syl
    @1
    @116
    @0
    @25
    @43
    cB
    cH
    cK
    cW
    dih1dimat.b
    dih1dimat.h
    lhpbase
    ad3antlr
    cB
    cK
    @113
    cW
    dih1dimat.b
    @113
    eqid
    opoccl
    syl2anc
    syl5eqel
    cB
    cT
    @46
    cH
    cK
    chlt
    cW
    cP
    dih1dimat.b
    dih1dimat.h
    dih1dimat.t
    ltrncl
    syl3anc
    cB
    @47
    cI
    fnfvelrn
    syl2anc
    eqeltrd
    pm2.61dane
    ralrimivva
    @14
    @22
    vv
    vf
    vs
    cT
    cE
    @4
    @19
    wceq
    #
    @6
    @21
    @11
    @117
    @5
    @20
    cN
    @4
    @19
    sneq
    fveq2d
    eleq1d
    ralxp
    sylibr
    r19.21bi
    syldan
    @6
    @11
    cD
    eleq1a
    syl
    rexlimdva
    adantr
    mpd
end
