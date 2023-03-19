include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "cfv.mm"
include "cin.mm"
include "wss.mm"
include "clat.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "latmle1.mm"
include "syl3anc.mm"
include "wb.mm"
include "simpl.mm"
include "latmcl.mm"
include "dihord.mm"
include "mpbird.mm"
include "latmle2.mm"
include "ssind.mm"
include "wrel.mm"
include "dihvalrel.mm"
include "relin1.mm"
include "syl.mm"
include "adantr.mm"
include "cv.mm"
include "cop.mm"
include "elin.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "lhpmcvr2.mm"
include "w3a.mm"
include "ccnv.mm"
include "ccom.mm"
include "vex.mm"
include "dihopelvalc.mm"
include "id.mm"
include "adantl.mm"
include "latref.mm"
include "syl2an.mm"
include "dihopelvalbN.mm"
include "syl12anc.mm"
include "3ad2ant1.mm"
include "anbi12d.mm"
include "simprll.mm"
include "cid.mm"
include "cres.mm"
include "simprrr.mm"
include "fveq1d.mm"
include "simpl1.mm"
include "lhpocnel2.mm"
include "simpl3l.mm"
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
include "syl2anc.mm"
include "f1of.mm"
include "fcoi1.mm"
include "3syl.mm"
include "fveq2d.mm"
include "simprlr.mm"
include "eqbrtrrd.mm"
include "trlle.mm"
include "simpl1l.mm"
include "trlcl.mm"
include "simpl2l.mm"
include "simpl1r.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "jca.mm"
include "mpbir2and.mm"
include "ex.mm"
include "sylbid.mm"
include "3expia.mm"
include "exp4c.mm"
include "imp4a.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "syl5bi.mm"
include "relssdv.mm"
include "eqssd.mm"

theorem dihglblem5apreN
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
  let c.0: class .0.
  let vq: setvar q
  let vf: setvar f
  let vs: setvar s
  let cY: class Y
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
  disjoint Y q
  disjoint Y s
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) ) -> ( I ` ( X ./\ W ) ) = ( ( I ` X ) i^i ( I ` W ) ) )

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
    wa
    #
    cX
    cW
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
    cW
    cI
    cfv
    #
    cin
    #
    @6
    @8
    @9
    @10
    @6
    @8
    @9
    wss
    #
    @7
    cX
    c.le
    wbr
    #
    @6
    cK
    clat
    wcel
    #
    @3
    cW
    cB
    wcel
    #
    @13
    @0
    @14
    @1
    @5
    cK
    hllat
    #
    ad2antrr
    #
    @2
    @3
    @4
    simprl
    #
    @1
    @15
    @0
    @5
    cB
    cH
    cK
    cW
    dihglblem5a.b
    dihglblem5a.h
    lhpbase
    #
    ad2antlr
    #
    cB
    cK
    c.le
    c.an
    cX
    cW
    dihglblem5a.b
    dihglblem5a.l
    dihglblem5a.m
    latmle1
    syl3anc
    @6
    @2
    @7
    cB
    wcel
    #
    @3
    @12
    @13
    wb
    @2
    @5
    simpl
    #
    @6
    @14
    @3
    @15
    @21
    @17
    @18
    @20
    cB
    cK
    c.an
    cX
    cW
    dihglblem5a.b
    dihglblem5a.m
    latmcl
    #
    syl3anc
    #
    @18
    cB
    cH
    cI
    cK
    c.le
    cW
    @7
    cX
    dihglblem5a.b
    dihglblem5a.l
    dihglblem5a.h
    dihglblem5a.i
    dihord
    syl3anc
    mpbird
    @6
    @8
    @10
    wss
    #
    @7
    cW
    c.le
    wbr
    #
    @6
    @14
    @3
    @15
    @26
    @17
    @18
    @20
    cB
    cK
    c.le
    c.an
    cX
    cW
    dihglblem5a.b
    dihglblem5a.l
    dihglblem5a.m
    latmle2
    #
    syl3anc
    @6
    @2
    @21
    @15
    @25
    @26
    wb
    @22
    @24
    @20
    cB
    cH
    cI
    cK
    c.le
    cW
    @7
    cW
    dihglblem5a.b
    dihglblem5a.l
    dihglblem5a.h
    dihglblem5a.i
    dihord
    syl3anc
    mpbird
    ssind
    @6
    vf
    vs
    @11
    @8
    @2
    @11
    wrel
    #
    @5
    @2
    @9
    wrel
    @28
    cH
    cI
    cK
    cW
    cX
    dihglblem5a.h
    dihglblem5a.i
    dihvalrel
    @9
    @10
    relin1
    syl
    adantr
    vf
    cv
    #
    vs
    cv
    #
    cop
    #
    @11
    wcel
    @31
    @9
    wcel
    #
    @31
    @10
    wcel
    #
    wa
    #
    @6
    @31
    @8
    wcel
    #
    @31
    @9
    @10
    elin
    @6
    vq
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @36
    @7
    c.or
    co
    cX
    wceq
    #
    wa
    #
    vq
    cA
    wrex
    @34
    @35
    wi
    #
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
    @6
    @39
    @40
    vq
    cA
    @6
    @36
    cA
    wcel
    #
    @37
    @38
    @40
    @6
    @41
    @37
    @38
    @40
    @2
    @5
    @41
    @37
    wa
    #
    @38
    wa
    #
    @40
    @2
    @5
    @43
    w3a
    #
    @34
    @29
    cT
    wcel
    #
    @30
    cE
    wcel
    wa
    #
    @29
    cG
    @30
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
    @45
    @29
    cR
    cfv
    #
    cW
    c.le
    wbr
    #
    wa
    #
    @30
    c.0
    wceq
    #
    wa
    #
    wa
    #
    @35
    @44
    @32
    @52
    @33
    @57
    cA
    cB
    cP
    @36
    cR
    @30
    cT
    vh
    cE
    @29
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
    @2
    @5
    @33
    @57
    wb
    #
    @43
    @2
    @2
    @15
    cW
    cW
    c.le
    wbr
    #
    @59
    @2
    id
    @1
    @15
    @0
    @19
    adantl
    @0
    @14
    @15
    @60
    @1
    @16
    @19
    cB
    cK
    c.le
    cW
    dihglblem5a.b
    dihglblem5a.l
    latref
    syl2an
    cB
    cR
    @30
    cT
    vh
    @29
    cH
    cI
    cK
    c.le
    c.0
    chlt
    cW
    cW
    dihglblem5a.b
    dihglblem5a.l
    dihglblem5a.h
    dihglblem5a.t
    dihglblem5a.r
    dihglblem5a.o
    dihglblem5a.i
    dihopelvalbN
    syl12anc
    3ad2ant1
    anbi12d
    @44
    @58
    @35
    @44
    @58
    wa
    #
    @35
    @45
    @53
    @7
    c.le
    wbr
    #
    wa
    #
    @56
    @61
    @45
    @62
    @58
    @45
    @44
    @52
    @45
    @54
    @56
    simprll
    adantl
    #
    @61
    @53
    cX
    c.le
    wbr
    #
    @54
    @62
    @61
    @50
    @53
    cX
    c.le
    @61
    @49
    @29
    cR
    @61
    @49
    @29
    cid
    cB
    cres
    #
    ccom
    #
    @29
    @61
    @48
    @66
    @29
    @61
    @48
    @66
    ccnv
    @66
    @61
    @47
    @66
    @61
    @47
    cG
    c.0
    cfv
    #
    @66
    @61
    cG
    @30
    c.0
    @44
    @52
    @55
    @56
    simprrr
    #
    fveq1d
    @61
    cG
    cT
    wcel
    #
    @68
    @66
    wceq
    @61
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
    @42
    @70
    @2
    @5
    @43
    @58
    simpl1
    #
    @61
    @2
    @71
    @72
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
    @42
    @38
    @2
    @5
    @58
    simpl3l
    cA
    cP
    @36
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
    syl3anc
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
    @61
    cB
    cB
    @29
    wf1o
    #
    cB
    cB
    @29
    wf
    @67
    @29
    wceq
    @61
    @2
    @45
    @73
    @72
    @64
    cB
    cT
    @29
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
    @29
    f1of
    cB
    cB
    @29
    fcoi1
    3syl
    eqtrd
    fveq2d
    @44
    @46
    @51
    @57
    simprlr
    eqbrtrrd
    @61
    @2
    @45
    @54
    @72
    @64
    cR
    cT
    @29
    cH
    cK
    c.le
    cW
    dihglblem5a.l
    dihglblem5a.h
    dihglblem5a.t
    dihglblem5a.r
    trlle
    syl2anc
    @61
    @14
    @53
    cB
    wcel
    #
    @3
    @15
    @65
    @54
    wa
    @62
    wb
    @61
    @0
    @14
    @0
    @1
    @5
    @43
    @58
    simpl1l
    @16
    syl
    #
    @61
    @2
    @45
    @74
    @72
    @64
    cB
    cR
    cT
    @29
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
    @43
    @58
    simpl2l
    #
    @61
    @1
    @15
    @0
    @1
    @5
    @43
    @58
    simpl1r
    @19
    syl
    #
    cB
    cK
    c.le
    c.an
    @53
    cX
    cW
    dihglblem5a.b
    dihglblem5a.l
    dihglblem5a.m
    latlem12
    syl13anc
    mpbi2and
    jca
    @69
    @61
    @2
    @21
    @26
    @35
    @63
    @56
    wa
    wb
    @72
    @61
    @14
    @3
    @15
    @21
    @75
    @76
    @77
    @23
    syl3anc
    @61
    @14
    @3
    @15
    @26
    @75
    @76
    @77
    @27
    syl3anc
    cB
    cR
    @30
    cT
    vh
    @29
    cH
    cI
    cK
    c.le
    c.0
    chlt
    cW
    @7
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
    ex
    sylbid
    3expia
    exp4c
    imp4a
    rexlimdv
    mpd
    syl5bi
    relssdv
    eqssd
end
