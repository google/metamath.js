include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cin.mm"
include "wss.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2l.mm"
include "simp3l.mm"
include "latmle1.mm"
include "syl3anc.mm"
include "wb.mm"
include "simp1.mm"
include "latmcl.mm"
include "dihord.mm"
include "mpbird.mm"
include "latmle2.mm"
include "ssind.mm"
include "wrel.mm"
include "dihvalrel.mm"
include "relin1.mm"
include "3ad2ant1.mm"
include "cv.mm"
include "cop.mm"
include "elin.mm"
include "wceq.mm"
include "wi.mm"
include "wrex.mm"
include "lhpmcvr2.mm"
include "3adant3.mm"
include "ccnv.mm"
include "ccom.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simprl.mm"
include "simprrl.mm"
include "jca.mm"
include "simprrr.mm"
include "vex.mm"
include "dihopelvalc.mm"
include "syl112anc.mm"
include "simpr.mm"
include "syl6bi.mm"
include "simpl3.mm"
include "dihopelvalbN.mm"
include "syl2anc.mm"
include "biimpd.mm"
include "simprll.mm"
include "3ad2ant3.mm"
include "cid.mm"
include "cres.mm"
include "simp3rr.mm"
include "fveq1d.mm"
include "simp11.mm"
include "lhpocnel2.mm"
include "simp2rl.mm"
include "ltrniotacl.mm"
include "tendo02.mm"
include "eqtrd.mm"
include "cnveqd.mm"
include "cnvresid.mm"
include "syl6eq.mm"
include "coeq2d.mm"
include "wf1o.mm"
include "wf.mm"
include "ltrn1o.mm"
include "f1of.mm"
include "fcoi1.mm"
include "3syl.mm"
include "fveq2d.mm"
include "eqbrtrrd.mm"
include "simprlr.mm"
include "simp11l.mm"
include "trlcl.mm"
include "simp12l.mm"
include "simp13l.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "simp13r.mm"
include "lattrd.mm"
include "syl12anc.mm"
include "mpbir2and.mm"
include "3expia.mm"
include "syl2and.mm"
include "rexlimddv.mm"
include "syl5bi.mm"
include "relssdv.mm"
include "eqssd.mm"

theorem dihmeetlem1N
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let vh: setvar h
  let cE: class E
  let cG: class G
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vq: setvar q
  let vf: setvar f
  let vs: setvar s
  assume dihglblem5a.b: |- B = ( Base ` K )
  assume dihglblem5a.m: |- ./\ = ( meet ` K )
  assume dihglblem5a.h: |- H = ( LHyp ` K )
  assume dihglblem5a.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihglblem5a.l: |- .<_ = ( le ` K )
  assume dihglblem5a.j: |- .\/ = ( join ` K )
  assume dihglblem5a.a: |- A = ( Atoms ` K )
  assume dihglblem5a.p: |- P = ( ( oc ` K ) ` W )
  assume dihglblem5a.t: |- T = ( ( LTrn ` K ) ` W )
  assume dihglblem5a.r: |- R = ( ( trL ` K ) ` W )
  assume dihglblem5a.e: |- E = ( ( TEndo ` K ) ` W )
  assume dihglblem5a.g: |- G = ( iota_ h e. T ( h ` P ) = q )
  assume dihglblem5a.o: |- .0. = ( h e. T |-> ( _I |` B ) )

  disjoint ./\ q
  disjoint h q
  disjoint .<_ h
  disjoint .<_ q
  disjoint A h
  disjoint A q
  disjoint B h
  disjoint B q
  disjoint H h
  disjoint H q
  disjoint I q
  disjoint K h
  disjoint K q
  disjoint P h
  disjoint T h
  disjoint W h
  disjoint W q
  disjoint X q
  disjoint Y q
  disjoint f q
  disjoint f s
  disjoint ./\ f
  disjoint q s
  disjoint ./\ s
  disjoint f h
  disjoint .<_ f
  disjoint h s
  disjoint .<_ s
  disjoint B f
  disjoint B s
  disjoint H f
  disjoint H s
  disjoint I f
  disjoint I s
  disjoint K f
  disjoint K s
  disjoint W f
  disjoint W s
  disjoint X f
  disjoint X s
  disjoint Y f
  disjoint Y s
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ ( Y e. B /\ Y .<_ W ) ) -> ( I ` ( X ./\ Y ) ) = ( ( I ` X ) i^i ( I ` Y ) ) )

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
    cY
    cB
    wcel
    #
    cY
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    cX
    cY
    c.an
    co
    #
    cI
    cfv
    #
    cX
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    cin
    #
    @9
    @11
    @12
    @13
    @9
    @11
    @12
    wss
    #
    @10
    cX
    c.le
    wbr
    #
    @9
    cK
    clat
    wcel
    #
    @3
    @6
    @16
    @9
    @0
    @17
    @0
    @1
    @5
    @8
    simp1l
    cK
    hllat
    #
    syl
    #
    @2
    @3
    @4
    @8
    simp2l
    #
    @2
    @5
    @6
    @7
    simp3l
    #
    cB
    cK
    c.le
    c.an
    cX
    cY
    dihglblem5a.b
    dihglblem5a.l
    dihglblem5a.m
    latmle1
    syl3anc
    @9
    @2
    @10
    cB
    wcel
    #
    @3
    @15
    @16
    wb
    @2
    @5
    @8
    simp1
    #
    @9
    @17
    @3
    @6
    @22
    @19
    @20
    @21
    cB
    cK
    c.an
    cX
    cY
    dihglblem5a.b
    dihglblem5a.m
    latmcl
    #
    syl3anc
    #
    @20
    cB
    cH
    cI
    cK
    c.le
    cW
    @10
    cX
    dihglblem5a.b
    dihglblem5a.l
    dihglblem5a.h
    dihglblem5a.i
    dihord
    syl3anc
    mpbird
    @9
    @11
    @13
    wss
    #
    @10
    cY
    c.le
    wbr
    #
    @9
    @17
    @3
    @6
    @27
    @19
    @20
    @21
    cB
    cK
    c.le
    c.an
    cX
    cY
    dihglblem5a.b
    dihglblem5a.l
    dihglblem5a.m
    latmle2
    #
    syl3anc
    @9
    @2
    @22
    @6
    @26
    @27
    wb
    @23
    @25
    @21
    cB
    cH
    cI
    cK
    c.le
    cW
    @10
    cY
    dihglblem5a.b
    dihglblem5a.l
    dihglblem5a.h
    dihglblem5a.i
    dihord
    syl3anc
    mpbird
    ssind
    @9
    vf
    vs
    @14
    @11
    @2
    @5
    @14
    wrel
    #
    @8
    @2
    @12
    wrel
    @29
    cH
    cI
    cK
    cW
    cX
    dihglblem5a.h
    dihglblem5a.i
    dihvalrel
    @12
    @13
    relin1
    syl
    3ad2ant1
    vf
    cv
    #
    vs
    cv
    #
    cop
    #
    @14
    wcel
    @32
    @12
    wcel
    #
    @32
    @13
    wcel
    #
    wa
    #
    @9
    @32
    @11
    wcel
    #
    @32
    @12
    @13
    elin
    @9
    vq
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @37
    cX
    cW
    c.an
    co
    c.or
    co
    cX
    wceq
    #
    wa
    #
    @35
    @36
    wi
    vq
    cA
    @2
    @5
    @40
    vq
    cA
    wrex
    @8
    cA
    cB
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    vq
    dihglblem5a.b
    dihglblem5a.l
    dihglblem5a.j
    dihglblem5a.m
    dihglblem5a.a
    dihglblem5a.h
    lhpmcvr2
    3adant3
    @9
    @37
    cA
    wcel
    #
    @40
    wa
    #
    wa
    #
    @33
    @30
    cG
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
    cX
    c.le
    wbr
    #
    @34
    @30
    cT
    wcel
    #
    @30
    cR
    cfv
    #
    cY
    c.le
    wbr
    #
    wa
    #
    @31
    c.0
    wceq
    #
    wa
    #
    @36
    @43
    @33
    @49
    @31
    cE
    wcel
    wa
    #
    @48
    wa
    #
    @48
    @43
    @2
    @5
    @41
    @38
    wa
    @39
    @33
    @56
    wb
    @2
    @5
    @8
    @42
    simpl1
    #
    @2
    @5
    @8
    @42
    simpl2
    @43
    @41
    @38
    @9
    @41
    @40
    simprl
    @9
    @41
    @38
    @39
    simprrl
    jca
    @9
    @41
    @38
    @39
    simprrr
    cA
    cB
    cP
    @37
    cR
    @31
    cT
    vh
    cE
    @30
    cG
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    cX
    dihglblem5a.b
    dihglblem5a.l
    dihglblem5a.j
    dihglblem5a.m
    dihglblem5a.a
    dihglblem5a.h
    dihglblem5a.p
    dihglblem5a.t
    dihglblem5a.r
    dihglblem5a.e
    dihglblem5a.i
    dihglblem5a.g
    vf
    vex
    vs
    vex
    dihopelvalc
    syl112anc
    @55
    @48
    simpr
    syl6bi
    @43
    @34
    @54
    @43
    @2
    @8
    @34
    @54
    wb
    @57
    @2
    @5
    @8
    @42
    simpl3
    cB
    cR
    @31
    cT
    vh
    @30
    cH
    cI
    cK
    c.le
    c.0
    chlt
    cW
    cY
    dihglblem5a.b
    dihglblem5a.l
    dihglblem5a.h
    dihglblem5a.t
    dihglblem5a.r
    dihglblem5a.o
    dihglblem5a.i
    dihopelvalbN
    syl2anc
    biimpd
    @9
    @42
    @48
    @54
    wa
    #
    @36
    @9
    @42
    @58
    w3a
    #
    @36
    @49
    @50
    @10
    c.le
    wbr
    #
    wa
    #
    @53
    @59
    @49
    @60
    @58
    @9
    @49
    @42
    @48
    @49
    @51
    @53
    simprll
    3ad2ant3
    #
    @59
    @50
    cX
    c.le
    wbr
    #
    @51
    @60
    @59
    @47
    @50
    cX
    c.le
    @59
    @46
    @30
    cR
    @59
    @46
    @30
    cid
    cB
    cres
    #
    ccom
    #
    @30
    @59
    @45
    @64
    @30
    @59
    @45
    @64
    ccnv
    @64
    @59
    @44
    @64
    @59
    @44
    cG
    c.0
    cfv
    #
    @64
    @59
    cG
    @31
    c.0
    @52
    @53
    @48
    @9
    @42
    simp3rr
    #
    fveq1d
    @59
    cG
    cT
    wcel
    #
    @66
    @64
    wceq
    @59
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
    @38
    @68
    @2
    @5
    @8
    @42
    @58
    simp11
    #
    @59
    @2
    @69
    @70
    cA
    cP
    cH
    cK
    c.le
    cW
    dihglblem5a.l
    dihglblem5a.a
    dihglblem5a.h
    dihglblem5a.p
    lhpocnel2
    syl
    @9
    @41
    @40
    @58
    simp2l
    @38
    @39
    @41
    @9
    @58
    simp2rl
    cA
    cP
    @37
    cT
    vh
    cG
    cH
    cK
    c.le
    cW
    dihglblem5a.l
    dihglblem5a.a
    dihglblem5a.h
    dihglblem5a.t
    dihglblem5a.g
    ltrniotacl
    syl112anc
    cB
    cT
    vh
    cG
    cK
    c.0
    dihglblem5a.o
    dihglblem5a.b
    tendo02
    syl
    eqtrd
    cnveqd
    cB
    cnvresid
    syl6eq
    coeq2d
    @59
    cB
    cB
    @30
    wf1o
    #
    cB
    cB
    @30
    wf
    @65
    @30
    wceq
    @59
    @2
    @49
    @71
    @70
    @62
    cB
    cT
    @30
    cH
    cK
    chlt
    cW
    dihglblem5a.b
    dihglblem5a.h
    dihglblem5a.t
    ltrn1o
    syl2anc
    cB
    cB
    @30
    f1of
    cB
    cB
    @30
    fcoi1
    3syl
    eqtrd
    fveq2d
    @9
    @42
    @48
    @54
    simp3l
    eqbrtrrd
    @58
    @9
    @51
    @42
    @48
    @49
    @51
    @53
    simprlr
    3ad2ant3
    @59
    @17
    @50
    cB
    wcel
    #
    @3
    @6
    @63
    @51
    wa
    @60
    wb
    @59
    @0
    @17
    @0
    @1
    @5
    @8
    @42
    @58
    simp11l
    @18
    syl
    #
    @59
    @2
    @49
    @72
    @70
    @62
    cB
    cR
    cT
    @30
    cH
    cK
    cW
    dihglblem5a.b
    dihglblem5a.h
    dihglblem5a.t
    dihglblem5a.r
    trlcl
    syl2anc
    @3
    @4
    @2
    @8
    @42
    @58
    simp12l
    #
    @6
    @7
    @2
    @5
    @42
    @58
    simp13l
    #
    cB
    cK
    c.le
    c.an
    @50
    cX
    cY
    dihglblem5a.b
    dihglblem5a.l
    dihglblem5a.m
    latlem12
    syl13anc
    mpbi2and
    jca
    @67
    @59
    @2
    @22
    @10
    cW
    c.le
    wbr
    @36
    @61
    @53
    wa
    wb
    @70
    @59
    @17
    @3
    @6
    @22
    @73
    @74
    @75
    @24
    syl3anc
    #
    @59
    cB
    cK
    c.le
    @10
    cY
    cW
    dihglblem5a.b
    dihglblem5a.l
    @73
    @76
    @75
    @59
    @1
    cW
    cB
    wcel
    @0
    @1
    @5
    @8
    @42
    @58
    simp11r
    cB
    cH
    cK
    cW
    dihglblem5a.b
    dihglblem5a.h
    lhpbase
    syl
    @59
    @17
    @3
    @6
    @27
    @73
    @74
    @75
    @28
    syl3anc
    @6
    @7
    @2
    @5
    @42
    @58
    simp13r
    lattrd
    cB
    cR
    @31
    cT
    vh
    @30
    cH
    cI
    cK
    c.le
    c.0
    chlt
    cW
    @10
    dihglblem5a.b
    dihglblem5a.l
    dihglblem5a.h
    dihglblem5a.t
    dihglblem5a.r
    dihglblem5a.o
    dihglblem5a.i
    dihopelvalbN
    syl12anc
    mpbir2and
    3expia
    syl2and
    rexlimddv
    syl5bi
    relssdv
    eqssd
end
