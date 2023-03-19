include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cin.mm"
include "wrel.mm"
include "csn.mm"
include "wceq.mm"
include "dihvalrel.mm"
include "relin1.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "cp0.mm"
include "eqid.mm"
include "dih0.mm"
include "releqd.mm"
include "mpbid.mm"
include "id.mm"
include "cv.mm"
include "cop.mm"
include "elin.mm"
include "cid.mm"
include "cres.mm"
include "wb.mm"
include "vex.mm"
include "dihopelvalcqat.mm"
include "3adant2.mm"
include "simp1.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "simp2l.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latmle2.mm"
include "dihopelvalbN.mm"
include "syl12anc.mm"
include "anbi12d.mm"
include "simprll.mm"
include "simprrr.mm"
include "fveq1d.mm"
include "simpl1.mm"
include "lhpocnel2.mm"
include "simpl3.mm"
include "ltrniotacl.mm"
include "tendo02.mm"
include "3eqtrd.mm"
include "jca.mm"
include "simprr.mm"
include "simprl.mm"
include "3eqtr4rd.mm"
include "tendo0cl.mm"
include "eqeltrd.mm"
include "idltrn.mm"
include "fveq2d.mm"
include "trlid0.mm"
include "eqtrd.mm"
include "cal.mm"
include "simpl1l.mm"
include "hlatl.mm"
include "adantr.mm"
include "atl0le.mm"
include "syl2anc.mm"
include "eqbrtrd.mm"
include "jca31.mm"
include "impbida.mm"
include "bitrd.mm"
include "opex.mm"
include "elsn.mm"
include "opth.mm"
include "bitr2i.mm"
include "syl6bb.mm"
include "dvh0g.mm"
include "sneqd.mm"
include "eleq2d.mm"
include "bitr4d.mm"
include "syl5bb.mm"
include "eqrelrdv2.mm"
include "syl21anc.mm"

theorem dihmeetlem4preN
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cO: class O
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vf: setvar f
  let vs: setvar s
  assume dihmeetlem4.b: |- B = ( Base ` K )
  assume dihmeetlem4.l: |- .<_ = ( le ` K )
  assume dihmeetlem4.m: |- ./\ = ( meet ` K )
  assume dihmeetlem4.a: |- A = ( Atoms ` K )
  assume dihmeetlem4.h: |- H = ( LHyp ` K )
  assume dihmeetlem4.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihmeetlem4.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihmeetlem4.z: |- .0. = ( 0g ` U )
  assume dihmeetlem4.g: |- G = ( iota_ g e. T ( g ` P ) = Q )
  assume dihmeetlem4.p: |- P = ( ( oc ` K ) ` W )
  assume dihmeetlem4.t: |- T = ( ( LTrn ` K ) ` W )
  assume dihmeetlem4.r: |- R = ( ( trL ` K ) ` W )
  assume dihmeetlem4.e: |- E = ( ( TEndo ` K ) ` W )
  assume dihmeetlem4.o: |- O = ( h e. T |-> ( _I |` B ) )

  disjoint .<_ g
  disjoint A g
  disjoint g h
  disjoint H g
  disjoint H h
  disjoint B h
  disjoint K g
  disjoint K h
  disjoint Q g
  disjoint T g
  disjoint T h
  disjoint W g
  disjoint W h
  disjoint P g
  disjoint f g
  disjoint f s
  disjoint .<_ f
  disjoint g s
  disjoint .<_ s
  disjoint ./\ f
  disjoint ./\ s
  disjoint A f
  disjoint A s
  disjoint f h
  disjoint H f
  disjoint h s
  disjoint H s
  disjoint I f
  disjoint I s
  disjoint B f
  disjoint B s
  disjoint K f
  disjoint K s
  disjoint Q f
  disjoint Q s
  disjoint W f
  disjoint W s
  disjoint X f
  disjoint X s
  disjoint .0. f
  disjoint .0. s
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( ( I ` Q ) i^i ( I ` ( X ./\ W ) ) ) = { .0. } )

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
    w3a
    #
    cQ
    cI
    cfv
    #
    cX
    cW
    c.an
    co
    #
    cI
    cfv
    #
    cin
    #
    wrel
    #
    c.0
    csn
    #
    wrel
    #
    @7
    @11
    @13
    wceq
    @2
    @5
    @12
    @6
    @2
    @8
    wrel
    @12
    cH
    cI
    cK
    cW
    cQ
    dihmeetlem4.h
    dihmeetlem4.i
    dihvalrel
    @8
    @10
    relin1
    syl
    3ad2ant1
    @2
    @5
    @14
    @6
    @2
    cK
    cp0
    cfv
    #
    cI
    cfv
    #
    wrel
    @14
    cH
    cI
    cK
    cW
    @15
    dihmeetlem4.h
    dihmeetlem4.i
    dihvalrel
    @2
    @16
    @13
    cU
    cH
    cI
    cK
    c.0
    cW
    @15
    @15
    eqid
    #
    dihmeetlem4.h
    dihmeetlem4.i
    dihmeetlem4.u
    dihmeetlem4.z
    dih0
    releqd
    mpbid
    3ad2ant1
    @7
    id
    @7
    vf
    vs
    @11
    @13
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
    @20
    @8
    wcel
    #
    @20
    @10
    wcel
    #
    wa
    #
    @7
    @20
    @13
    wcel
    #
    @20
    @8
    @10
    elin
    @7
    @23
    @20
    cid
    cB
    cres
    #
    cO
    cop
    #
    csn
    #
    wcel
    #
    @24
    @7
    @23
    @18
    @25
    wceq
    #
    @19
    cO
    wceq
    #
    wa
    #
    @28
    @7
    @23
    @18
    cG
    @19
    cfv
    #
    wceq
    #
    @19
    cE
    wcel
    #
    wa
    #
    @18
    cT
    wcel
    #
    @18
    cR
    cfv
    #
    @9
    c.le
    wbr
    #
    wa
    #
    @30
    wa
    #
    wa
    #
    @31
    @7
    @21
    @35
    @22
    @40
    @2
    @6
    @21
    @35
    wb
    @5
    cA
    cP
    cQ
    @19
    cT
    vg
    cE
    @18
    cG
    cH
    cI
    cK
    c.le
    cW
    dihmeetlem4.l
    dihmeetlem4.a
    dihmeetlem4.h
    dihmeetlem4.p
    dihmeetlem4.t
    dihmeetlem4.e
    dihmeetlem4.i
    dihmeetlem4.g
    vf
    vex
    #
    vs
    vex
    #
    dihopelvalcqat
    3adant2
    @7
    @2
    @9
    cB
    wcel
    #
    @9
    cW
    c.le
    wbr
    #
    @22
    @40
    wb
    @2
    @5
    @6
    simp1
    @7
    cK
    clat
    wcel
    #
    @3
    cW
    cB
    wcel
    #
    @44
    @7
    @0
    @46
    @0
    @1
    @5
    @6
    simp1l
    cK
    hllat
    syl
    #
    @2
    @3
    @4
    @6
    simp2l
    #
    @7
    @1
    @47
    @0
    @1
    @5
    @6
    simp1r
    cB
    cH
    cK
    cW
    dihmeetlem4.b
    dihmeetlem4.h
    lhpbase
    syl
    #
    cB
    cK
    c.an
    cX
    cW
    dihmeetlem4.b
    dihmeetlem4.m
    latmcl
    syl3anc
    #
    @7
    @46
    @3
    @47
    @45
    @48
    @49
    @50
    cB
    cK
    c.le
    c.an
    cX
    cW
    dihmeetlem4.b
    dihmeetlem4.l
    dihmeetlem4.m
    latmle2
    syl3anc
    cB
    cR
    @19
    cT
    vh
    @18
    cH
    cI
    cK
    c.le
    cO
    chlt
    cW
    @9
    dihmeetlem4.b
    dihmeetlem4.l
    dihmeetlem4.h
    dihmeetlem4.t
    dihmeetlem4.r
    dihmeetlem4.o
    dihmeetlem4.i
    dihopelvalbN
    syl12anc
    anbi12d
    @7
    @41
    @31
    @7
    @41
    wa
    #
    @29
    @30
    @52
    @18
    @32
    cG
    cO
    cfv
    #
    @25
    @7
    @33
    @34
    @40
    simprll
    @52
    cG
    @19
    cO
    @7
    @35
    @39
    @30
    simprrr
    #
    fveq1d
    @52
    cG
    cT
    wcel
    #
    @53
    @25
    wceq
    #
    @52
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
    @55
    @2
    @5
    @6
    @41
    simpl1
    #
    @52
    @2
    @57
    @58
    cA
    cP
    cH
    cK
    c.le
    cW
    dihmeetlem4.l
    dihmeetlem4.a
    dihmeetlem4.h
    dihmeetlem4.p
    lhpocnel2
    #
    syl
    @2
    @5
    @6
    @41
    simpl3
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
    dihmeetlem4.l
    dihmeetlem4.a
    dihmeetlem4.h
    dihmeetlem4.t
    dihmeetlem4.g
    ltrniotacl
    #
    syl3anc
    cB
    cT
    vh
    cG
    cK
    cO
    dihmeetlem4.o
    dihmeetlem4.b
    tendo02
    #
    syl
    3eqtrd
    @54
    jca
    @7
    @31
    wa
    #
    @33
    @34
    @40
    @62
    @53
    @25
    @32
    @18
    @62
    @55
    @56
    @62
    @2
    @57
    @6
    @55
    @2
    @5
    @6
    @31
    simpl1
    #
    @62
    @2
    @57
    @63
    @59
    syl
    @2
    @5
    @6
    @31
    simpl3
    @60
    syl3anc
    @61
    syl
    @62
    cG
    @19
    cO
    @7
    @29
    @30
    simprr
    #
    fveq1d
    @7
    @29
    @30
    simprl
    #
    3eqtr4rd
    @62
    @19
    cO
    cE
    @64
    @62
    @2
    cO
    cE
    wcel
    @63
    cB
    cT
    vh
    cE
    cH
    cK
    cO
    cW
    dihmeetlem4.b
    dihmeetlem4.h
    dihmeetlem4.t
    dihmeetlem4.e
    dihmeetlem4.o
    tendo0cl
    syl
    eqeltrd
    @62
    @36
    @38
    @30
    @62
    @18
    @25
    cT
    @65
    @62
    @2
    @25
    cT
    wcel
    @63
    cB
    cT
    cH
    cK
    cW
    dihmeetlem4.b
    dihmeetlem4.h
    dihmeetlem4.t
    idltrn
    syl
    eqeltrd
    @62
    @37
    @15
    @9
    c.le
    @62
    @37
    @25
    cR
    cfv
    #
    @15
    @62
    @18
    @25
    cR
    @65
    fveq2d
    @62
    @2
    @66
    @15
    wceq
    @63
    cB
    cR
    cH
    cK
    cW
    @15
    dihmeetlem4.b
    @17
    dihmeetlem4.h
    dihmeetlem4.r
    trlid0
    syl
    eqtrd
    @62
    cK
    cal
    wcel
    #
    @44
    @15
    @9
    c.le
    wbr
    @62
    @0
    @67
    @0
    @1
    @5
    @6
    @31
    simpl1l
    cK
    hlatl
    syl
    @7
    @44
    @31
    @51
    adantr
    cB
    cK
    c.le
    @9
    @15
    dihmeetlem4.b
    dihmeetlem4.l
    @17
    atl0le
    syl2anc
    eqbrtrd
    @64
    jca31
    jca31
    impbida
    bitrd
    @28
    @20
    @26
    wceq
    @31
    @20
    @26
    @18
    @19
    opex
    elsn
    @18
    @19
    @25
    cO
    @42
    @43
    opth
    bitr2i
    syl6bb
    @7
    @13
    @27
    @20
    @7
    c.0
    @26
    @2
    @5
    c.0
    @26
    wceq
    @6
    cB
    cT
    cU
    vh
    cH
    cK
    cO
    cW
    c.0
    dihmeetlem4.b
    dihmeetlem4.h
    dihmeetlem4.t
    dihmeetlem4.u
    dihmeetlem4.z
    dihmeetlem4.o
    dvh0g
    3ad2ant1
    sneqd
    eleq2d
    bitr4d
    syl5bb
    eqrelrdv2
    syl21anc
end
