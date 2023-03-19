include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wrel.mm"
include "cv.mm"
include "ciin.mm"
include "wceq.mm"
include "dihvalrel.mm"
include "3ad2ant1.mm"
include "wrex.mm"
include "wex.mm"
include "simp2r.mm"
include "n0.mm"
include "sylib.mm"
include "simpr.mm"
include "simpl1.mm"
include "syl.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"
include "df-rex.mm"
include "sylibr.mm"
include "reliin.mm"
include "id.mm"
include "co.mm"
include "cop.mm"
include "wb.mm"
include "simp1.mm"
include "ccla.mm"
include "simp1l.mm"
include "hlclat.mm"
include "simp2l.mm"
include "clatglbcl.mm"
include "syl2anc.mm"
include "simp3.mm"
include "lhpmcvr2.mm"
include "syl12anc.mm"
include "ccnv.mm"
include "ccom.mm"
include "adantr.mm"
include "simpl3.mm"
include "vex.mm"
include "dihopelvalc.mm"
include "syl121anc.mm"
include "wral.mm"
include "simpl2r.mm"
include "r19.28zv.mm"
include "simp11.mm"
include "simp12l.mm"
include "sseldd.mm"
include "simp13.mm"
include "simp11l.mm"
include "clatglble.mm"
include "syl3anc.mm"
include "clat.mm"
include "wi.mm"
include "hllat.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "lattr.mm"
include "syl13anc.mm"
include "mpand.mm"
include "mtod.mm"
include "cp1.mm"
include "simp2ll.mm"
include "atbase.mm"
include "latmcl.mm"
include "latlej1.mm"
include "breqtrd.mm"
include "lattrd.mm"
include "atmod3i1.mm"
include "syl131anc.mm"
include "eqid.mm"
include "lhpjat2.mm"
include "oveq2d.mm"
include "col.mm"
include "hlol.mm"
include "olm11.mm"
include "3eqtrd.mm"
include "syl122anc.mm"
include "3expa.mm"
include "ralbidva.mm"
include "simp3l.mm"
include "simp3r.mm"
include "lhpocnel2.mm"
include "ltrniotacl.mm"
include "tendocl.mm"
include "ltrncnv.mm"
include "ltrnco.mm"
include "trlcl.mm"
include "clatleglb.mm"
include "pm5.32da.mm"
include "3bitr4rd.mm"
include "cvv.mm"
include "opex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "syl6bbr.mm"
include "bitrd.mm"
include "exp44.mm"
include "imp4a.mm"
include "rexlimdv.mm"
include "eqrelrdv2.mm"
include "syl21anc.mm"

theorem dihglbcpreN
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vq: setvar q
  let vf: setvar f
  let vs: setvar s
  assume dihglbc.b: |- B = ( Base ` K )
  assume dihglbc.g: |- G = ( glb ` K )
  assume dihglbc.h: |- H = ( LHyp ` K )
  assume dihglbc.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihglbc.l: |- .<_ = ( le ` K )
  assume dihglbcpre.j: |- .\/ = ( join ` K )
  assume dihglbcpre.m: |- ./\ = ( meet ` K )
  assume dihglbcpre.a: |- A = ( Atoms ` K )
  assume dihglbcpre.p: |- P = ( ( oc ` K ) ` W )
  assume dihglbcpre.t: |- T = ( ( LTrn ` K ) ` W )
  assume dihglbcpre.r: |- R = ( ( trL ` K ) ` W )
  assume dihglbcpre.e: |- E = ( ( TEndo ` K ) ` W )
  assume dihglbcpre.f: |- F = ( iota_ g e. T ( g ` P ) = q )

  disjoint q x
  disjoint ./\ q
  disjoint ./\ x
  disjoint g q
  disjoint g x
  disjoint .<_ g
  disjoint .<_ q
  disjoint .<_ x
  disjoint .\/ x
  disjoint A g
  disjoint A q
  disjoint A x
  disjoint B q
  disjoint B x
  disjoint E x
  disjoint F x
  disjoint G q
  disjoint G x
  disjoint H g
  disjoint H q
  disjoint H x
  disjoint I q
  disjoint K g
  disjoint K q
  disjoint K x
  disjoint P g
  disjoint R x
  disjoint S q
  disjoint S x
  disjoint T g
  disjoint T x
  disjoint W g
  disjoint W q
  disjoint W x
  disjoint f g
  disjoint f q
  disjoint f s
  disjoint f x
  disjoint .<_ f
  disjoint g s
  disjoint q s
  disjoint s x
  disjoint .<_ s
  disjoint B f
  disjoint B s
  disjoint G f
  disjoint G s
  disjoint H f
  disjoint H s
  disjoint I f
  disjoint I s
  disjoint K f
  disjoint K s
  disjoint S f
  disjoint S s
  disjoint W f
  disjoint W s
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( S C_ B /\ S =/= (/) ) /\ -. ( G ` S ) .<_ W ) -> ( I ` ( G ` S ) ) = |^|_ x e. S ( I ` x ) )

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
    cS
    cB
    wss
    #
    cS
    c0
    wne
    #
    wa
    #
    cS
    cG
    cfv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    @6
    cI
    cfv
    #
    wrel
    #
    vx
    cS
    vx
    cv
    #
    cI
    cfv
    #
    ciin
    #
    wrel
    #
    @9
    @10
    @14
    wceq
    @2
    @5
    @11
    @8
    cH
    cI
    cK
    cW
    @6
    dihglbc.h
    dihglbc.i
    dihvalrel
    3ad2ant1
    @9
    @13
    wrel
    #
    vx
    cS
    wrex
    #
    @15
    @9
    @12
    cS
    wcel
    #
    @16
    wa
    #
    vx
    wex
    #
    @17
    @9
    @18
    vx
    wex
    #
    @20
    @9
    @4
    @21
    @2
    @3
    @4
    @8
    simp2r
    vx
    cS
    n0
    sylib
    @9
    @18
    @19
    vx
    @9
    @18
    @19
    @9
    @18
    wa
    #
    @18
    @16
    @9
    @18
    simpr
    @22
    @2
    @16
    @2
    @5
    @8
    @18
    simpl1
    cH
    cI
    cK
    cW
    @12
    dihglbc.h
    dihglbc.i
    dihvalrel
    syl
    jca
    ex
    eximdv
    mpd
    @16
    vx
    cS
    df-rex
    sylibr
    vx
    cS
    @13
    reliin
    syl
    @9
    id
    @9
    vf
    vs
    @10
    @14
    @9
    vq
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @23
    @6
    cW
    c.an
    co
    #
    c.or
    co
    #
    @6
    wceq
    #
    wa
    #
    vq
    cA
    wrex
    #
    vf
    cv
    #
    vs
    cv
    #
    cop
    #
    @10
    wcel
    #
    @32
    @14
    wcel
    #
    wb
    #
    @9
    @2
    @6
    cB
    wcel
    #
    @8
    @29
    @2
    @5
    @8
    simp1
    @9
    cK
    ccla
    wcel
    #
    @3
    @36
    @9
    @0
    @37
    @0
    @1
    @5
    @8
    simp1l
    cK
    hlclat
    #
    syl
    @2
    @3
    @4
    @8
    simp2l
    cB
    cS
    cG
    cK
    dihglbc.b
    dihglbc.g
    clatglbcl
    syl2anc
    #
    @2
    @5
    @8
    simp3
    cA
    cB
    cH
    c.or
    cK
    c.le
    c.an
    cW
    @6
    vq
    dihglbc.b
    dihglbc.l
    dihglbcpre.j
    dihglbcpre.m
    dihglbcpre.a
    dihglbc.h
    lhpmcvr2
    syl12anc
    @9
    @28
    @35
    vq
    cA
    @9
    @23
    cA
    wcel
    #
    @24
    @27
    @35
    @9
    @40
    @24
    @27
    @35
    @9
    @40
    @24
    wa
    #
    @27
    wa
    #
    wa
    #
    @33
    @30
    cT
    wcel
    #
    @31
    cE
    wcel
    #
    wa
    #
    @30
    cF
    @31
    cfv
    #
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    @6
    c.le
    wbr
    #
    wa
    #
    @34
    @43
    @2
    @36
    @8
    @42
    @33
    @52
    wb
    @2
    @5
    @8
    @42
    simpl1
    @9
    @36
    @42
    @39
    adantr
    @2
    @5
    @8
    @42
    simpl3
    @9
    @42
    simpr
    cA
    cB
    cP
    @23
    cR
    @31
    cT
    vg
    cE
    @30
    cF
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    @6
    dihglbc.b
    dihglbc.l
    dihglbcpre.j
    dihglbcpre.m
    dihglbcpre.a
    dihglbc.h
    dihglbcpre.p
    dihglbcpre.t
    dihglbcpre.r
    dihglbcpre.e
    dihglbc.i
    dihglbcpre.f
    vf
    vex
    #
    vs
    vex
    #
    dihopelvalc
    syl121anc
    @43
    @52
    @32
    @13
    wcel
    #
    vx
    cS
    wral
    #
    @34
    @43
    @46
    @50
    @12
    c.le
    wbr
    #
    wa
    #
    vx
    cS
    wral
    #
    @46
    @57
    vx
    cS
    wral
    #
    wa
    #
    @56
    @52
    @43
    @4
    @59
    @61
    wb
    @3
    @4
    @2
    @8
    @42
    simpl2r
    @46
    @57
    vx
    cS
    r19.28zv
    syl
    @43
    @55
    @58
    vx
    cS
    @9
    @42
    @18
    @55
    @58
    wb
    #
    @9
    @42
    @18
    w3a
    #
    @2
    @12
    cB
    wcel
    #
    @12
    cW
    c.le
    wbr
    #
    wn
    @41
    @23
    @12
    cW
    c.an
    co
    c.or
    co
    #
    @12
    wceq
    @62
    @2
    @5
    @8
    @42
    @18
    simp11
    #
    @63
    cS
    cB
    @12
    @3
    @4
    @2
    @8
    @42
    @18
    simp12l
    #
    @9
    @42
    @18
    simp3
    #
    sseldd
    #
    @63
    @65
    @7
    @2
    @5
    @8
    @42
    @18
    simp13
    @63
    @6
    @12
    c.le
    wbr
    #
    @65
    @7
    @63
    @37
    @3
    @18
    @71
    @63
    @0
    @37
    @0
    @1
    @5
    @8
    @42
    @18
    simp11l
    #
    @38
    syl
    @68
    @69
    cB
    cS
    cG
    cK
    c.le
    @12
    dihglbc.b
    dihglbc.l
    dihglbc.g
    clatglble
    syl3anc
    #
    @63
    cK
    clat
    wcel
    #
    @36
    @64
    cW
    cB
    wcel
    #
    @71
    @65
    wa
    @7
    wi
    @63
    @0
    @74
    @72
    cK
    hllat
    syl
    #
    @9
    @42
    @36
    @18
    @39
    3ad2ant1
    #
    @70
    @63
    @1
    @75
    @0
    @1
    @5
    @8
    @42
    @18
    simp11r
    cB
    cH
    cK
    cW
    dihglbc.b
    dihglbc.h
    lhpbase
    syl
    #
    cB
    cK
    c.le
    @6
    @12
    cW
    dihglbc.b
    dihglbc.l
    lattr
    syl13anc
    mpand
    mtod
    @9
    @41
    @27
    @18
    simp2l
    #
    @63
    @66
    @12
    @23
    cW
    c.or
    co
    #
    c.an
    co
    #
    @12
    cK
    cp1
    cfv
    #
    c.an
    co
    #
    @12
    @63
    @0
    @40
    @64
    @75
    @23
    @12
    c.le
    wbr
    @66
    @81
    wceq
    @72
    @40
    @24
    @27
    @9
    @18
    simp2ll
    #
    @70
    @78
    @63
    cB
    cK
    c.le
    @23
    @6
    @12
    dihglbc.b
    dihglbc.l
    @76
    @63
    @40
    @23
    cB
    wcel
    #
    @84
    cA
    cB
    @23
    cK
    dihglbc.b
    dihglbcpre.a
    atbase
    syl
    #
    @77
    @70
    @63
    @23
    @26
    @6
    c.le
    @63
    @74
    @85
    @25
    cB
    wcel
    #
    @23
    @26
    c.le
    wbr
    @76
    @86
    @63
    @74
    @36
    @75
    @87
    @76
    @77
    @78
    cB
    cK
    c.an
    @6
    cW
    dihglbc.b
    dihglbcpre.m
    latmcl
    syl3anc
    cB
    c.or
    cK
    c.le
    @23
    @25
    dihglbc.b
    dihglbc.l
    dihglbcpre.j
    latlej1
    syl3anc
    @9
    @41
    @27
    @18
    simp2r
    breqtrd
    @73
    lattrd
    cA
    cB
    @23
    c.or
    cK
    c.le
    c.an
    @12
    cW
    dihglbc.b
    dihglbc.l
    dihglbcpre.j
    dihglbcpre.m
    dihglbcpre.a
    atmod3i1
    syl131anc
    @63
    @80
    @82
    @12
    c.an
    @63
    @2
    @41
    @80
    @82
    wceq
    @67
    @79
    cA
    @23
    @82
    cH
    c.or
    cK
    c.le
    cW
    dihglbc.l
    dihglbcpre.j
    @82
    eqid
    #
    dihglbcpre.a
    dihglbc.h
    lhpjat2
    syl2anc
    oveq2d
    @63
    cK
    col
    wcel
    #
    @64
    @83
    @12
    wceq
    @63
    @0
    @89
    @72
    cK
    hlol
    syl
    @70
    cB
    @82
    cK
    c.an
    @12
    dihglbc.b
    dihglbcpre.m
    @88
    olm11
    syl2anc
    3eqtrd
    cA
    cB
    cP
    @23
    cR
    @31
    cT
    vg
    cE
    @30
    cF
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    @12
    dihglbc.b
    dihglbc.l
    dihglbcpre.j
    dihglbcpre.m
    dihglbcpre.a
    dihglbc.h
    dihglbcpre.p
    dihglbcpre.t
    dihglbcpre.r
    dihglbcpre.e
    dihglbc.i
    dihglbcpre.f
    @53
    @54
    dihopelvalc
    syl122anc
    3expa
    ralbidva
    @43
    @46
    @51
    @60
    @9
    @42
    @46
    @51
    @60
    wb
    #
    @9
    @42
    @46
    w3a
    #
    @37
    @50
    cB
    wcel
    #
    @3
    @90
    @91
    @0
    @37
    @0
    @1
    @5
    @8
    @42
    @46
    simp11l
    @38
    syl
    @91
    @2
    @49
    cT
    wcel
    #
    @92
    @2
    @5
    @8
    @42
    @46
    simp11
    #
    @91
    @2
    @44
    @48
    cT
    wcel
    #
    @93
    @94
    @9
    @42
    @44
    @45
    simp3l
    @91
    @2
    @47
    cT
    wcel
    #
    @95
    @94
    @91
    @2
    @45
    cF
    cT
    wcel
    #
    @96
    @94
    @9
    @42
    @44
    @45
    simp3r
    @91
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
    @41
    @97
    @94
    @91
    @2
    @98
    @94
    cA
    cP
    cH
    cK
    c.le
    cW
    dihglbc.l
    dihglbcpre.a
    dihglbc.h
    dihglbcpre.p
    lhpocnel2
    syl
    @9
    @41
    @27
    @46
    simp2l
    cA
    cP
    @23
    cT
    vg
    cF
    cH
    cK
    c.le
    cW
    dihglbc.l
    dihglbcpre.a
    dihglbc.h
    dihglbcpre.t
    dihglbcpre.f
    ltrniotacl
    syl3anc
    @31
    cT
    cE
    cF
    cH
    cK
    chlt
    cW
    dihglbc.h
    dihglbcpre.t
    dihglbcpre.e
    tendocl
    syl3anc
    cT
    @47
    cH
    cK
    cW
    dihglbc.h
    dihglbcpre.t
    ltrncnv
    syl2anc
    cT
    @30
    @48
    cH
    cK
    cW
    dihglbc.h
    dihglbcpre.t
    ltrnco
    syl3anc
    cB
    cR
    cT
    @49
    cH
    cK
    cW
    dihglbc.b
    dihglbc.h
    dihglbcpre.t
    dihglbcpre.r
    trlcl
    syl2anc
    @3
    @4
    @2
    @8
    @42
    @46
    simp12l
    vx
    cB
    cS
    cG
    cK
    c.le
    @50
    dihglbc.b
    dihglbc.l
    dihglbc.g
    clatleglb
    syl3anc
    3expa
    pm5.32da
    3bitr4rd
    @32
    cvv
    wcel
    @34
    @56
    wb
    @30
    @31
    opex
    vx
    @32
    cS
    @13
    cvv
    eliin
    ax-mp
    syl6bbr
    bitrd
    exp44
    imp4a
    rexlimdv
    mpd
    eqrelrdv2
    syl21anc
end
