include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "cin.mm"
include "csn.mm"
include "wrel.mm"
include "dihvalrel.mm"
include "3ad2ant1.mm"
include "relin1.mm"
include "syl.mm"
include "cv.mm"
include "cop.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "elin.mm"
include "wb.mm"
include "simp1.mm"
include "simp2l.mm"
include "vex.mm"
include "dihopelvalcqat.mm"
include "syl2anc.mm"
include "simp2r.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "simprll.mm"
include "simpl3.mm"
include "fveq1.mm"
include "simpl1.mm"
include "lhpocnel2.mm"
include "simpl2l.mm"
include "ltrniotaval.mm"
include "syl3anc.mm"
include "simpl2r.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "necon3d.mm"
include "mpd.mm"
include "simp2ll.mm"
include "simp2rl.mm"
include "eqtr3d.mm"
include "simp11.mm"
include "simp2rr.mm"
include "simp3.mm"
include "simp12l.mm"
include "ltrniotacl.mm"
include "simp12r.mm"
include "tendospcanN.mm"
include "syl122anc.mm"
include "mpbid.mm"
include "3expia.mm"
include "necon1d.mm"
include "fveq1d.mm"
include "tendo02.mm"
include "3eqtrd.mm"
include "jca.mm"
include "ex.mm"
include "sylbid.mm"
include "dvh0g.mm"
include "sneqd.mm"
include "eleq2d.mm"
include "opex.mm"
include "elsn.mm"
include "opth.mm"
include "bitr2i.mm"
include "syl6rbbr.mm"
include "sylibd.mm"
include "relssdv.mm"
include "clmod.mm"
include "clss.mm"
include "wss.mm"
include "dvhlmod.mm"
include "atbase.mm"
include "eqid.mm"
include "dihlss.mm"
include "lssincl.mm"
include "lss0ss.mm"
include "eqssd.mm"

theorem dihmeetlem13N
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cO: class O
  let cW: class W
  let c.0: class .0.
  let vf: setvar f
  let vs: setvar s
  assume dihmeetlem13.b: |- B = ( Base ` K )
  assume dihmeetlem13.l: |- .<_ = ( le ` K )
  assume dihmeetlem13.j: |- .\/ = ( join ` K )
  assume dihmeetlem13.a: |- A = ( Atoms ` K )
  assume dihmeetlem13.h: |- H = ( LHyp ` K )
  assume dihmeetlem13.p: |- P = ( ( oc ` K ) ` W )
  assume dihmeetlem13.t: |- T = ( ( LTrn ` K ) ` W )
  assume dihmeetlem13.e: |- E = ( ( TEndo ` K ) ` W )
  assume dihmeetlem13.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume dihmeetlem13.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihmeetlem13.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihmeetlem13.z: |- .0. = ( 0g ` U )
  assume dihmeetlem13.f: |- F = ( iota_ h e. T ( h ` P ) = Q )
  assume dihmeetlem13.g: |- G = ( iota_ h e. T ( h ` P ) = R )

  disjoint .<_ h
  disjoint A h
  disjoint B h
  disjoint H h
  disjoint K h
  disjoint P h
  disjoint Q h
  disjoint R h
  disjoint T h
  disjoint W h
  disjoint f h
  disjoint f s
  disjoint .<_ f
  disjoint h s
  disjoint .<_ s
  disjoint A f
  disjoint A s
  disjoint H f
  disjoint H s
  disjoint I f
  disjoint I s
  disjoint K f
  disjoint K s
  disjoint Q f
  disjoint Q s
  disjoint R f
  disjoint R s
  disjoint W f
  disjoint W s
  disjoint .0. f
  disjoint .0. s
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ Q =/= R ) -> ( ( I ` Q ) i^i ( I ` R ) ) = { .0. } )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
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
    cR
    cA
    wcel
    #
    cR
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cQ
    cR
    wne
    #
    w3a
    #
    cQ
    cI
    cfv
    #
    cR
    cI
    cfv
    #
    cin
    #
    c.0
    csn
    #
    @9
    vf
    vs
    @12
    @13
    @9
    @10
    wrel
    #
    @12
    wrel
    @0
    @7
    @14
    @8
    cH
    cI
    cK
    cW
    cQ
    dihmeetlem13.h
    dihmeetlem13.i
    dihvalrel
    3ad2ant1
    @10
    @11
    relin1
    syl
    @9
    vf
    cv
    #
    vs
    cv
    #
    cop
    #
    @12
    wcel
    #
    @15
    cid
    cB
    cres
    #
    wceq
    #
    @16
    cO
    wceq
    #
    wa
    #
    @17
    @13
    wcel
    #
    @9
    @18
    @15
    cF
    @16
    cfv
    #
    wceq
    #
    @16
    cE
    wcel
    #
    wa
    #
    @15
    cG
    @16
    cfv
    #
    wceq
    #
    @26
    wa
    #
    wa
    #
    @22
    @18
    @17
    @10
    wcel
    #
    @17
    @11
    wcel
    #
    wa
    @9
    @31
    @17
    @10
    @11
    elin
    @9
    @32
    @27
    @33
    @30
    @9
    @0
    @3
    @32
    @27
    wb
    @0
    @7
    @8
    simp1
    #
    @0
    @3
    @6
    @8
    simp2l
    cA
    cP
    cQ
    @16
    cT
    vh
    cE
    @15
    cF
    cH
    cI
    cK
    c.le
    cW
    dihmeetlem13.l
    dihmeetlem13.a
    dihmeetlem13.h
    dihmeetlem13.p
    dihmeetlem13.t
    dihmeetlem13.e
    dihmeetlem13.i
    dihmeetlem13.f
    vf
    vex
    #
    vs
    vex
    #
    dihopelvalcqat
    syl2anc
    @9
    @0
    @6
    @33
    @30
    wb
    @34
    @0
    @3
    @6
    @8
    simp2r
    cA
    cP
    cR
    @16
    cT
    vh
    cE
    @15
    cG
    cH
    cI
    cK
    c.le
    cW
    dihmeetlem13.l
    dihmeetlem13.a
    dihmeetlem13.h
    dihmeetlem13.p
    dihmeetlem13.t
    dihmeetlem13.e
    dihmeetlem13.i
    dihmeetlem13.g
    @35
    @36
    dihopelvalcqat
    syl2anc
    anbi12d
    syl5bb
    @9
    @31
    @22
    @9
    @31
    wa
    #
    @20
    @21
    @37
    @15
    @24
    cF
    cO
    cfv
    #
    @19
    @9
    @25
    @26
    @30
    simprll
    @37
    cF
    @16
    cO
    @37
    cF
    cG
    wne
    #
    @21
    @37
    @8
    @39
    @0
    @7
    @8
    @31
    simpl3
    @37
    cF
    cG
    cQ
    cR
    cF
    cG
    wceq
    #
    cP
    cF
    cfv
    #
    cP
    cG
    cfv
    #
    wceq
    @37
    cQ
    cR
    wceq
    cP
    cF
    cG
    fveq1
    @37
    @41
    cQ
    @42
    cR
    @37
    @0
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
    @3
    @41
    cQ
    wceq
    @0
    @7
    @8
    @31
    simpl1
    #
    @37
    @0
    @43
    @44
    cA
    cP
    cH
    cK
    c.le
    cW
    dihmeetlem13.l
    dihmeetlem13.a
    dihmeetlem13.h
    dihmeetlem13.p
    lhpocnel2
    #
    syl
    #
    @3
    @6
    @0
    @8
    @31
    simpl2l
    #
    cA
    cP
    cQ
    cT
    vh
    cF
    cH
    cK
    c.le
    cW
    dihmeetlem13.l
    dihmeetlem13.a
    dihmeetlem13.h
    dihmeetlem13.t
    dihmeetlem13.f
    ltrniotaval
    syl3anc
    @37
    @0
    @43
    @6
    @42
    cR
    wceq
    @44
    @46
    @3
    @6
    @0
    @8
    @31
    simpl2r
    cA
    cP
    cR
    cT
    vh
    cG
    cH
    cK
    c.le
    cW
    dihmeetlem13.l
    dihmeetlem13.a
    dihmeetlem13.h
    dihmeetlem13.t
    dihmeetlem13.g
    ltrniotaval
    syl3anc
    eqeq12d
    syl5ib
    necon3d
    mpd
    @37
    @16
    cO
    cF
    cG
    @9
    @31
    @16
    cO
    wne
    #
    @40
    @9
    @31
    @48
    w3a
    #
    @24
    @28
    wceq
    #
    @40
    @49
    @15
    @24
    @28
    @25
    @26
    @30
    @9
    @48
    simp2ll
    @29
    @26
    @27
    @9
    @48
    simp2rl
    eqtr3d
    @49
    @0
    @26
    @48
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    @50
    @40
    wb
    @0
    @7
    @8
    @31
    @48
    simp11
    #
    @29
    @26
    @27
    @9
    @48
    simp2rr
    @9
    @31
    @48
    simp3
    @49
    @0
    @43
    @3
    @51
    @53
    @49
    @0
    @43
    @53
    @45
    syl
    #
    @3
    @6
    @0
    @8
    @31
    @48
    simp12l
    cA
    cP
    cQ
    cT
    vh
    cF
    cH
    cK
    c.le
    cW
    dihmeetlem13.l
    dihmeetlem13.a
    dihmeetlem13.h
    dihmeetlem13.t
    dihmeetlem13.f
    ltrniotacl
    #
    syl3anc
    @49
    @0
    @43
    @6
    @52
    @53
    @54
    @3
    @6
    @0
    @8
    @31
    @48
    simp12r
    cA
    cP
    cR
    cT
    vh
    cG
    cH
    cK
    c.le
    cW
    dihmeetlem13.l
    dihmeetlem13.a
    dihmeetlem13.h
    dihmeetlem13.t
    dihmeetlem13.g
    ltrniotacl
    syl3anc
    cB
    @16
    cT
    vh
    cE
    cF
    cG
    cH
    cK
    cO
    cW
    dihmeetlem13.b
    dihmeetlem13.h
    dihmeetlem13.t
    dihmeetlem13.e
    dihmeetlem13.o
    tendospcanN
    syl122anc
    mpbid
    3expia
    necon1d
    mpd
    #
    fveq1d
    @37
    @51
    @38
    @19
    wceq
    @37
    @0
    @43
    @3
    @51
    @44
    @46
    @47
    @55
    syl3anc
    cB
    cT
    vh
    cF
    cK
    cO
    dihmeetlem13.o
    dihmeetlem13.b
    tendo02
    syl
    3eqtrd
    @56
    jca
    ex
    sylbid
    @9
    @23
    @17
    @19
    cO
    cop
    #
    csn
    #
    wcel
    #
    @22
    @9
    @13
    @58
    @17
    @9
    c.0
    @57
    @0
    @7
    c.0
    @57
    wceq
    @8
    cB
    cT
    cU
    vh
    cH
    cK
    cO
    cW
    c.0
    dihmeetlem13.b
    dihmeetlem13.h
    dihmeetlem13.t
    dihmeetlem13.u
    dihmeetlem13.z
    dihmeetlem13.o
    dvh0g
    3ad2ant1
    sneqd
    eleq2d
    @59
    @17
    @57
    wceq
    @22
    @17
    @57
    @15
    @16
    opex
    elsn
    @15
    @16
    @19
    cO
    @35
    @36
    opth
    bitr2i
    syl6rbbr
    sylibd
    relssdv
    @9
    cU
    clmod
    wcel
    #
    @12
    cU
    clss
    cfv
    #
    wcel
    #
    @13
    @12
    wss
    @9
    cU
    cH
    cK
    cW
    dihmeetlem13.h
    dihmeetlem13.u
    @34
    dvhlmod
    #
    @9
    @60
    @10
    @61
    wcel
    #
    @11
    @61
    wcel
    #
    @62
    @63
    @9
    @0
    cQ
    cB
    wcel
    #
    @64
    @34
    @9
    @1
    @66
    @1
    @2
    @6
    @0
    @8
    simp2ll
    cA
    cB
    cQ
    cK
    dihmeetlem13.b
    dihmeetlem13.a
    atbase
    syl
    cB
    @61
    cU
    cH
    cI
    cK
    cW
    cQ
    dihmeetlem13.b
    dihmeetlem13.h
    dihmeetlem13.i
    dihmeetlem13.u
    @61
    eqid
    #
    dihlss
    syl2anc
    @9
    @0
    cR
    cB
    wcel
    #
    @65
    @34
    @9
    @4
    @68
    @4
    @5
    @3
    @0
    @8
    simp2rl
    cA
    cB
    cR
    cK
    dihmeetlem13.b
    dihmeetlem13.a
    atbase
    syl
    cB
    @61
    cU
    cH
    cI
    cK
    cW
    cR
    dihmeetlem13.b
    dihmeetlem13.h
    dihmeetlem13.i
    dihmeetlem13.u
    @67
    dihlss
    syl2anc
    @61
    @10
    @11
    cU
    @67
    lssincl
    syl3anc
    @61
    cU
    @12
    c.0
    dihmeetlem13.z
    @67
    lss0ss
    syl2anc
    eqssd
end
