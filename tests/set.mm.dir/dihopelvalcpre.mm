include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cop.mm"
include "cfv.mm"
include "cv.mm"
include "wex.mm"
include "ccnv.mm"
include "ccom.mm"
include "dihvalcq.mm"
include "eleq2d.mm"
include "wb.mm"
include "simp1.mm"
include "simp3l.mm"
include "diclss.mm"
include "syl2anc.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2l.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latmle2.mm"
include "diblss.mm"
include "syl12anc.mm"
include "dvhopellsm.mm"
include "vex.mm"
include "dicopelval2.mm"
include "dibopelval3.mm"
include "anbi12d.mm"
include "anbi1d.mm"
include "csca.mm"
include "cplusg.mm"
include "simpl1.mm"
include "simprll.mm"
include "simprlr.mm"
include "lhpocnel2.mm"
include "simpl3l.mm"
include "ltrniotacl.mm"
include "tendocl.mm"
include "eqeltrd.mm"
include "adantl.mm"
include "simprrr.mm"
include "tendo0cl.mm"
include "eqid.mm"
include "dvhopvadd.mm"
include "syl122anc.mm"
include "dvhfplusr.mm"
include "oveqd.mm"
include "opeq2d.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "opth.mm"
include "oveq2d.mm"
include "tendo0plr.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "simplll.mm"
include "fveq1d.mm"
include "eqtr4d.mm"
include "eqcomd.mm"
include "coass.mm"
include "cid.mm"
include "cres.mm"
include "wf1o.mm"
include "simpllr.mm"
include "adantrr.mm"
include "ltrn1o.mm"
include "f1ococnv1.mm"
include "coeq1d.mm"
include "wf.mm"
include "ad2antrl.mm"
include "f1of.mm"
include "fcoi2.mm"
include "3syl.mm"
include "eqtr2d.mm"
include "simprrl.mm"
include "ltrncnv.mm"
include "ltrnco.mm"
include "ltrncom.mm"
include "3eqtr4a.mm"
include "simplrr.mm"
include "jca.mm"
include "jca31.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "simpll1.mm"
include "adantr.mm"
include "simpl1l.mm"
include "trlcl.mm"
include "simpl2l.mm"
include "simpl1r.mm"
include "latmle1.mm"
include "lattrd.mm"
include "eqeltrrd.mm"
include "simprr.mm"
include "trlle.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "coeq2d.mm"
include "fcoi1.mm"
include "syl6eqr.mm"
include "coeq12d.mm"
include "impbida.mm"
include "df-3an.mm"
include "syl6bbr.mm"
include "3bitrd.mm"
include "4exbidv.mm"
include "fvex.mm"
include "cnvex.mm"
include "coex.mm"
include "cmpt.mm"
include "cvv.mm"
include "cltrn.mm"
include "eqeltri.mm"
include "mptex.mm"
include "biidd.mm"
include "eleq1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "ceqsex4v.mm"
include "syl6bb.mm"

theorem dihopelvalcpre
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume dihopelvalcp.b: |- B = ( Base ` K )
  assume dihopelvalcp.l: |- .<_ = ( le ` K )
  assume dihopelvalcp.j: |- .\/ = ( join ` K )
  assume dihopelvalcp.m: |- ./\ = ( meet ` K )
  assume dihopelvalcp.a: |- A = ( Atoms ` K )
  assume dihopelvalcp.h: |- H = ( LHyp ` K )
  assume dihopelvalcp.p: |- P = ( ( oc ` K ) ` W )
  assume dihopelvalcp.t: |- T = ( ( LTrn ` K ) ` W )
  assume dihopelvalcp.r: |- R = ( ( trL ` K ) ` W )
  assume dihopelvalcp.e: |- E = ( ( TEndo ` K ) ` W )
  assume dihopelvalcp.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihopelvalcp.g: |- G = ( iota_ g e. T ( g ` P ) = Q )
  assume dihopelvalcp.f: |- F e. _V
  assume dihopelvalcp.s: |- S e. _V
  assume dihopelvalcp.z: |- Z = ( h e. T |-> ( _I |` B ) )
  assume dihopelvalcp.n: |- N = ( ( DIsoB ` K ) ` W )
  assume dihopelvalcp.c: |- C = ( ( DIsoC ` K ) ` W )
  assume dihopelvalcp.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihopelvalcp.d: |- .+ = ( +g ` U )
  assume dihopelvalcp.v: |- V = ( LSubSp ` U )
  assume dihopelvalcp.y: |- .(+) = ( LSSum ` U )
  assume dihopelvalcp.o: |- O = ( a e. E , b e. E |-> ( h e. T |-> ( ( a ` h ) o. ( b ` h ) ) ) )

  disjoint .<_ g
  disjoint A g
  disjoint P g
  disjoint a b
  disjoint E a
  disjoint E b
  disjoint g h
  disjoint H g
  disjoint H h
  disjoint a g
  disjoint a h
  disjoint K a
  disjoint b g
  disjoint b h
  disjoint K b
  disjoint K g
  disjoint K h
  disjoint B h
  disjoint T a
  disjoint T b
  disjoint T g
  disjoint T h
  disjoint W a
  disjoint W b
  disjoint W g
  disjoint W h
  disjoint Q g
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .+ w
  disjoint x y
  disjoint x z
  disjoint .+ x
  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint .\/ w
  disjoint .\/ x
  disjoint .\/ y
  disjoint .\/ z
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint .<_ w
  disjoint .<_ x
  disjoint .<_ y
  disjoint .<_ z
  disjoint ./\ w
  disjoint ./\ x
  disjoint ./\ y
  disjoint ./\ z
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint V x
  disjoint V y
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint E w
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint H w
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint Q w
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint Z w
  disjoint Z x
  disjoint Z y
  disjoint Z z
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( Q .\/ ( X ./\ W ) ) = X ) ) -> ( <. F , S >. e. ( I ` X ) <-> ( ( F e. T /\ S e. E ) /\ ( R ` ( F o. `' ( S ` G ) ) ) .<_ X ) ) )

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
    cX
    cB
    wcel
    #
    cX
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    cQ
    cX
    cW
    c.an
    co
    #
    c.or
    co
    cX
    wceq
    #
    wa
    #
    w3a
    #
    cF
    cS
    cop
    #
    cX
    cI
    cfv
    #
    wcel
    @11
    cQ
    cC
    cfv
    #
    @7
    cN
    cfv
    #
    c.po
    co
    #
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @13
    wcel
    #
    vz
    cv
    #
    vw
    cv
    #
    cop
    #
    @14
    wcel
    #
    wa
    #
    @11
    @19
    @23
    c.pl
    co
    #
    wceq
    #
    wa
    #
    vw
    wex
    vz
    wex
    vy
    wex
    vx
    wex
    #
    cF
    cT
    wcel
    #
    cS
    cE
    wcel
    #
    wa
    #
    cF
    cG
    cS
    cfv
    #
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    cX
    c.le
    wbr
    #
    wa
    #
    @10
    @12
    @15
    @11
    cA
    cB
    cC
    cN
    c.po
    cQ
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    cX
    dihopelvalcp.b
    dihopelvalcp.l
    dihopelvalcp.j
    dihopelvalcp.m
    dihopelvalcp.a
    dihopelvalcp.h
    dihopelvalcp.i
    dihopelvalcp.n
    dihopelvalcp.c
    dihopelvalcp.u
    dihopelvalcp.y
    dihvalcq
    eleq2d
    @10
    @2
    @13
    cV
    wcel
    #
    @14
    cV
    wcel
    #
    @16
    @29
    wb
    @2
    @5
    @9
    simp1
    #
    @10
    @2
    @6
    @39
    @41
    @2
    @5
    @6
    @8
    simp3l
    #
    cA
    cQ
    cV
    cU
    cH
    cC
    cK
    c.le
    cW
    dihopelvalcp.l
    dihopelvalcp.a
    dihopelvalcp.h
    dihopelvalcp.u
    dihopelvalcp.c
    dihopelvalcp.v
    diclss
    syl2anc
    @10
    @2
    @7
    cB
    wcel
    #
    @7
    cW
    c.le
    wbr
    #
    @40
    @41
    @10
    cK
    clat
    wcel
    #
    @3
    cW
    cB
    wcel
    #
    @43
    @10
    @0
    @45
    @0
    @1
    @5
    @9
    simp1l
    cK
    hllat
    #
    syl
    #
    @2
    @3
    @4
    @9
    simp2l
    #
    @10
    @1
    @46
    @0
    @1
    @5
    @9
    simp1r
    cB
    cH
    cK
    cW
    dihopelvalcp.b
    dihopelvalcp.h
    lhpbase
    #
    syl
    #
    cB
    cK
    c.an
    cX
    cW
    dihopelvalcp.b
    dihopelvalcp.m
    latmcl
    #
    syl3anc
    #
    @10
    @45
    @3
    @46
    @44
    @48
    @49
    @51
    cB
    cK
    c.le
    c.an
    cX
    cW
    dihopelvalcp.b
    dihopelvalcp.l
    dihopelvalcp.m
    latmle2
    syl3anc
    #
    cB
    cV
    cU
    cH
    cN
    cK
    c.le
    cW
    @7
    dihopelvalcp.b
    dihopelvalcp.l
    dihopelvalcp.h
    dihopelvalcp.u
    dihopelvalcp.n
    dihopelvalcp.v
    diblss
    syl12anc
    vx
    vy
    vz
    vw
    c.pl
    c.po
    cV
    cS
    cU
    cF
    cH
    cK
    cW
    @13
    @14
    dihopelvalcp.h
    dihopelvalcp.u
    dihopelvalcp.d
    dihopelvalcp.v
    dihopelvalcp.y
    dvhopellsm
    syl3anc
    @10
    @29
    @17
    @33
    wceq
    #
    @18
    cS
    wceq
    #
    wa
    #
    @21
    @35
    wceq
    #
    @22
    cZ
    wceq
    #
    wa
    #
    @30
    @18
    cE
    wcel
    #
    wa
    #
    @21
    cR
    cfv
    #
    cX
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    vw
    wex
    vz
    wex
    vy
    wex
    vx
    wex
    @38
    @10
    @28
    @66
    vx
    vy
    vz
    vw
    @10
    @28
    @17
    cG
    @18
    cfv
    #
    wceq
    #
    @61
    wa
    #
    @21
    cT
    wcel
    #
    @63
    @7
    c.le
    wbr
    #
    wa
    #
    @59
    wa
    #
    wa
    #
    @27
    wa
    #
    @57
    @60
    wa
    #
    @74
    cF
    @17
    @21
    ccom
    #
    wceq
    #
    cS
    @18
    wceq
    #
    wa
    #
    wa
    #
    wa
    #
    @66
    @10
    @25
    @74
    @27
    @10
    @20
    @69
    @24
    @73
    @10
    @2
    @6
    @20
    @69
    wb
    @41
    @42
    cA
    cP
    cQ
    @18
    cT
    vg
    cE
    @17
    cG
    cH
    cC
    cK
    c.le
    chlt
    cW
    dihopelvalcp.l
    dihopelvalcp.a
    dihopelvalcp.h
    dihopelvalcp.p
    dihopelvalcp.t
    dihopelvalcp.e
    dihopelvalcp.c
    dihopelvalcp.g
    vx
    vex
    vy
    vex
    dicopelval2
    syl2anc
    @10
    @2
    @43
    @44
    @24
    @73
    wb
    @41
    @53
    @54
    cB
    cR
    @22
    cT
    vh
    @21
    cH
    cN
    cK
    c.le
    chlt
    cW
    @7
    cZ
    dihopelvalcp.b
    dihopelvalcp.l
    dihopelvalcp.h
    dihopelvalcp.t
    dihopelvalcp.r
    dihopelvalcp.z
    dihopelvalcp.n
    dibopelval3
    syl12anc
    anbi12d
    anbi1d
    @10
    @75
    @81
    @82
    @10
    @74
    @27
    @80
    @10
    @74
    wa
    #
    @27
    @11
    @77
    @18
    @22
    cO
    co
    #
    cop
    #
    wceq
    #
    @80
    @83
    @26
    @85
    @11
    @83
    @26
    @77
    @18
    @22
    cU
    csca
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cop
    #
    @85
    @83
    @2
    @17
    cT
    wcel
    #
    @61
    @70
    @22
    cE
    wcel
    @26
    @90
    wceq
    @2
    @5
    @9
    @74
    simpl1
    #
    @83
    @17
    @67
    cT
    @10
    @68
    @61
    @73
    simprll
    @83
    @2
    @61
    cG
    cT
    wcel
    #
    @67
    cT
    wcel
    #
    @92
    @10
    @68
    @61
    @73
    simprlr
    #
    @83
    @2
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    @6
    @93
    @92
    @83
    @2
    @96
    @92
    cA
    cP
    cH
    cK
    c.le
    cW
    dihopelvalcp.l
    dihopelvalcp.a
    dihopelvalcp.h
    dihopelvalcp.p
    lhpocnel2
    #
    syl
    @6
    @8
    @2
    @5
    @74
    simpl3l
    cA
    cP
    cQ
    cT
    vg
    cG
    cH
    cK
    c.le
    cW
    dihopelvalcp.l
    dihopelvalcp.a
    dihopelvalcp.h
    dihopelvalcp.t
    dihopelvalcp.g
    ltrniotacl
    #
    syl3anc
    #
    @18
    cT
    cE
    cG
    cH
    cK
    chlt
    cW
    dihopelvalcp.h
    dihopelvalcp.t
    dihopelvalcp.e
    tendocl
    #
    syl3anc
    eqeltrd
    @95
    @74
    @70
    @10
    @69
    @70
    @71
    @59
    simprll
    #
    adantl
    @83
    @22
    cZ
    cE
    @10
    @69
    @72
    @59
    simprrr
    #
    @83
    @2
    cZ
    cE
    wcel
    @92
    cB
    cT
    vh
    cE
    cH
    cK
    cZ
    cW
    dihopelvalcp.b
    dihopelvalcp.h
    dihopelvalcp.t
    dihopelvalcp.e
    dihopelvalcp.z
    tendo0cl
    syl
    eqeltrd
    @87
    c.pl
    @88
    @18
    @22
    cT
    cU
    cE
    @17
    @21
    cH
    cK
    cW
    dihopelvalcp.h
    dihopelvalcp.t
    dihopelvalcp.e
    dihopelvalcp.u
    @87
    eqid
    #
    dihopelvalcp.d
    @88
    eqid
    #
    dvhopvadd
    syl122anc
    @83
    @89
    @84
    @77
    @83
    @88
    cO
    @18
    @22
    @83
    @2
    @88
    cO
    wceq
    @92
    vb
    cO
    @88
    cT
    cU
    vh
    cE
    @87
    cH
    cK
    chlt
    cW
    va
    dihopelvalcp.h
    dihopelvalcp.t
    dihopelvalcp.e
    dihopelvalcp.u
    @103
    dihopelvalcp.o
    @104
    dvhfplusr
    syl
    oveqd
    opeq2d
    eqtrd
    eqeq2d
    @86
    @78
    cS
    @84
    wceq
    #
    wa
    @83
    @80
    cF
    cS
    @77
    @84
    dihopelvalcp.f
    dihopelvalcp.s
    opth
    @83
    @105
    @79
    @78
    @83
    @84
    @18
    cS
    @83
    @84
    @18
    cZ
    cO
    co
    #
    @18
    @83
    @22
    cZ
    @18
    cO
    @102
    oveq2d
    @83
    @2
    @61
    @106
    @18
    wceq
    @92
    @95
    vb
    cB
    cO
    @18
    cT
    vh
    cE
    cH
    cK
    cZ
    cW
    va
    dihopelvalcp.b
    dihopelvalcp.h
    dihopelvalcp.t
    dihopelvalcp.e
    dihopelvalcp.z
    dihopelvalcp.o
    tendo0plr
    syl2anc
    eqtrd
    eqeq2d
    anbi2d
    syl5bb
    bitrd
    pm5.32da
    @10
    @81
    @76
    @10
    @81
    @76
    @10
    @81
    wa
    #
    @55
    @56
    @60
    @107
    @17
    @67
    @33
    @81
    @68
    @10
    @68
    @61
    @73
    @80
    simplll
    #
    adantl
    @107
    cG
    cS
    @18
    @10
    @74
    @78
    @79
    simprrr
    #
    fveq1d
    eqtr4d
    #
    @107
    cS
    @18
    @109
    eqcomd
    @107
    @58
    @59
    @107
    @34
    @33
    ccom
    #
    @21
    ccom
    #
    @34
    @33
    @21
    ccom
    #
    ccom
    #
    @21
    @35
    @34
    @33
    @21
    coass
    @107
    @112
    cid
    cB
    cres
    #
    @21
    ccom
    #
    @21
    @107
    @111
    @115
    @21
    @107
    cB
    cB
    @33
    wf1o
    #
    @111
    @115
    wceq
    #
    @107
    @2
    @33
    cT
    wcel
    #
    @117
    @2
    @5
    @9
    @81
    simpl1
    #
    @107
    @2
    @31
    @93
    @119
    @120
    @107
    cS
    @18
    cE
    @109
    @81
    @61
    @10
    @68
    @61
    @73
    @80
    simpllr
    #
    adantl
    eqeltrd
    @10
    @74
    @93
    @80
    @99
    adantrr
    cS
    cT
    cE
    cG
    cH
    cK
    chlt
    cW
    dihopelvalcp.h
    dihopelvalcp.t
    dihopelvalcp.e
    tendocl
    #
    syl3anc
    #
    cB
    cT
    @33
    cH
    cK
    chlt
    cW
    dihopelvalcp.b
    dihopelvalcp.h
    dihopelvalcp.t
    ltrn1o
    #
    syl2anc
    cB
    cB
    @33
    f1ococnv1
    #
    syl
    coeq1d
    @107
    cB
    cB
    @21
    wf1o
    #
    cB
    cB
    @21
    wf
    @116
    @21
    wceq
    @107
    @2
    @70
    @126
    @120
    @74
    @70
    @10
    @80
    @101
    ad2antrl
    #
    cB
    cT
    @21
    cH
    cK
    chlt
    cW
    dihopelvalcp.b
    dihopelvalcp.h
    dihopelvalcp.t
    ltrn1o
    syl2anc
    cB
    cB
    @21
    f1of
    cB
    cB
    @21
    fcoi2
    3syl
    eqtr2d
    @107
    @35
    @113
    @34
    ccom
    #
    @114
    @107
    cF
    @113
    @34
    @107
    cF
    @77
    @113
    @10
    @74
    @78
    @79
    simprrl
    @107
    @17
    @33
    @21
    @110
    coeq1d
    eqtrd
    coeq1d
    @107
    @2
    @34
    cT
    wcel
    #
    @113
    cT
    wcel
    #
    @114
    @128
    wceq
    @120
    @107
    @2
    @119
    @129
    @120
    @123
    cT
    @33
    cH
    cK
    cW
    dihopelvalcp.h
    dihopelvalcp.t
    ltrncnv
    #
    syl2anc
    @107
    @2
    @119
    @70
    @130
    @120
    @123
    @127
    cT
    @33
    @21
    cH
    cK
    cW
    dihopelvalcp.h
    dihopelvalcp.t
    ltrnco
    syl3anc
    cT
    @34
    @113
    cH
    cK
    cW
    dihopelvalcp.h
    dihopelvalcp.t
    ltrncom
    syl3anc
    eqtr4d
    3eqtr4a
    @81
    @59
    @10
    @69
    @72
    @59
    @80
    simplrr
    adantl
    jca
    jca31
    ex
    pm4.71rd
    bitrd
    @10
    @82
    @76
    @65
    wa
    @66
    @10
    @76
    @81
    @65
    @10
    @76
    wa
    #
    @81
    @65
    @132
    @81
    wa
    #
    @30
    @61
    @64
    @133
    cF
    @77
    cT
    @132
    @74
    @78
    @79
    simprrl
    @133
    @2
    @91
    @70
    @77
    cT
    wcel
    @2
    @5
    @9
    @76
    @81
    simpll1
    #
    @133
    @17
    @67
    cT
    @81
    @68
    @132
    @108
    adantl
    @133
    @2
    @61
    @93
    @94
    @134
    @81
    @61
    @132
    @121
    adantl
    #
    @133
    @2
    @96
    @6
    @93
    @134
    @133
    @2
    @96
    @134
    @97
    syl
    @132
    @6
    @81
    @6
    @8
    @2
    @5
    @76
    simpl3l
    #
    adantr
    @98
    syl3anc
    @100
    syl3anc
    eqeltrd
    @74
    @70
    @132
    @80
    @101
    ad2antrl
    #
    cT
    @17
    @21
    cH
    cK
    cW
    dihopelvalcp.h
    dihopelvalcp.t
    ltrnco
    syl3anc
    eqeltrd
    @135
    @133
    cB
    cK
    c.le
    @63
    @7
    cX
    dihopelvalcp.b
    dihopelvalcp.l
    @133
    @0
    @45
    @132
    @0
    @81
    @0
    @1
    @5
    @9
    @76
    simpl1l
    #
    adantr
    @47
    syl
    #
    @133
    @2
    @70
    @63
    cB
    wcel
    #
    @134
    @137
    cB
    cR
    cT
    @21
    cH
    cK
    cW
    dihopelvalcp.b
    dihopelvalcp.h
    dihopelvalcp.t
    dihopelvalcp.r
    trlcl
    #
    syl2anc
    @133
    @45
    @3
    @46
    @43
    @139
    @132
    @3
    @81
    @3
    @4
    @2
    @9
    @76
    simpl2l
    #
    adantr
    #
    @133
    @1
    @46
    @132
    @1
    @81
    @0
    @1
    @5
    @9
    @76
    simpl1r
    #
    adantr
    @50
    syl
    #
    @52
    syl3anc
    @143
    @74
    @71
    @132
    @80
    @69
    @70
    @71
    @59
    simprlr
    ad2antrl
    @133
    @45
    @3
    @46
    @7
    cX
    c.le
    wbr
    @139
    @143
    @145
    cB
    cK
    c.le
    c.an
    cX
    cW
    dihopelvalcp.b
    dihopelvalcp.l
    dihopelvalcp.m
    latmle1
    syl3anc
    lattrd
    jca31
    @132
    @65
    wa
    #
    @69
    @73
    @80
    @146
    @68
    @61
    @146
    @17
    @33
    @67
    @132
    @55
    @65
    @10
    @55
    @56
    @60
    simprll
    adantr
    #
    @146
    cG
    @18
    cS
    @132
    @56
    @65
    @10
    @55
    @56
    @60
    simprlr
    adantr
    #
    fveq1d
    eqtr4d
    @132
    @30
    @61
    @64
    simprlr
    #
    jca
    @146
    @70
    @71
    @59
    @146
    @21
    @35
    cT
    @132
    @58
    @65
    @10
    @57
    @58
    @59
    simprrl
    adantr
    #
    @146
    @2
    @30
    @129
    @35
    cT
    wcel
    #
    @2
    @5
    @9
    @76
    @65
    simpll1
    #
    @132
    @30
    @61
    @64
    simprll
    #
    @146
    @2
    @119
    @129
    @152
    @146
    @2
    @31
    @93
    @119
    @152
    @146
    @18
    cS
    cE
    @148
    @149
    eqeltrrd
    @146
    @2
    @96
    @6
    @93
    @152
    @146
    @2
    @96
    @152
    @97
    syl
    @132
    @6
    @65
    @136
    adantr
    @98
    syl3anc
    @122
    syl3anc
    #
    @131
    syl2anc
    cT
    cF
    @34
    cH
    cK
    cW
    dihopelvalcp.h
    dihopelvalcp.t
    ltrnco
    syl3anc
    #
    eqeltrd
    #
    @146
    @64
    @63
    cW
    c.le
    wbr
    #
    @71
    @132
    @62
    @64
    simprr
    @146
    @2
    @70
    @157
    @152
    @156
    cR
    cT
    @21
    cH
    cK
    c.le
    cW
    dihopelvalcp.l
    dihopelvalcp.h
    dihopelvalcp.t
    dihopelvalcp.r
    trlle
    syl2anc
    @146
    @45
    @140
    @3
    @46
    @64
    @157
    wa
    @71
    wb
    @146
    @0
    @45
    @132
    @0
    @65
    @138
    adantr
    @47
    syl
    @146
    @2
    @70
    @140
    @152
    @156
    @141
    syl2anc
    @132
    @3
    @65
    @142
    adantr
    @146
    @1
    @46
    @132
    @1
    @65
    @144
    adantr
    @50
    syl
    cB
    cK
    c.le
    c.an
    @63
    cX
    cW
    dihopelvalcp.b
    dihopelvalcp.l
    dihopelvalcp.m
    latlem12
    syl13anc
    mpbi2and
    @132
    @59
    @65
    @10
    @57
    @58
    @59
    simprrr
    adantr
    jca31
    @146
    @78
    @79
    @146
    cF
    @33
    @35
    ccom
    #
    @77
    @146
    cF
    @35
    @33
    ccom
    #
    @158
    @146
    cF
    cF
    @111
    ccom
    #
    @159
    @146
    @160
    cF
    @115
    ccom
    #
    cF
    @146
    @111
    @115
    cF
    @146
    @117
    @118
    @146
    @2
    @119
    @117
    @152
    @154
    @124
    syl2anc
    @125
    syl
    coeq2d
    @146
    cB
    cB
    cF
    wf1o
    #
    cB
    cB
    cF
    wf
    @161
    cF
    wceq
    @146
    @2
    @30
    @162
    @152
    @153
    cB
    cT
    cF
    cH
    cK
    chlt
    cW
    dihopelvalcp.b
    dihopelvalcp.h
    dihopelvalcp.t
    ltrn1o
    syl2anc
    cB
    cB
    cF
    f1of
    cB
    cB
    cF
    fcoi1
    3syl
    eqtr2d
    cF
    @34
    @33
    coass
    syl6eqr
    @146
    @2
    @119
    @151
    @158
    @159
    wceq
    @152
    @154
    @155
    cT
    @33
    @35
    cH
    cK
    cW
    dihopelvalcp.h
    dihopelvalcp.t
    ltrncom
    syl3anc
    eqtr4d
    @146
    @17
    @33
    @21
    @35
    @147
    @150
    coeq12d
    eqtr4d
    @146
    @18
    cS
    @148
    eqcomd
    jca
    jca31
    impbida
    pm5.32da
    @57
    @60
    @65
    df-3an
    syl6bbr
    3bitrd
    4exbidv
    @65
    @65
    @32
    @64
    wa
    @38
    @38
    vx
    vy
    vz
    vw
    @33
    cS
    @35
    cZ
    cG
    cS
    fvex
    #
    dihopelvalcp.s
    cF
    @34
    dihopelvalcp.f
    @33
    @163
    cnvex
    coex
    cZ
    vh
    cT
    @115
    cmpt
    cvv
    dihopelvalcp.z
    vh
    cT
    @115
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    dihopelvalcp.t
    cW
    @164
    fvex
    eqeltri
    mptex
    eqeltri
    @55
    @65
    biidd
    @56
    @62
    @32
    @64
    @56
    @61
    @31
    @30
    @18
    cS
    cE
    eleq1
    anbi2d
    anbi1d
    @58
    @64
    @37
    @32
    @58
    @63
    @36
    cX
    c.le
    @21
    @35
    cR
    fveq2
    breq1d
    anbi2d
    @59
    @38
    biidd
    ceqsex4v
    syl6bb
    3bitrd
end
