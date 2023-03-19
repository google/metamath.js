include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "cop.mm"
include "cvsca.mm"
include "co.mm"
include "wceq.mm"
include "csca.mm"
include "cbs.mm"
include "wrex.mm"
include "cab.mm"
include "csn.mm"
include "ctendo.mm"
include "cxp.mm"
include "crab.mm"
include "df-rab.mm"
include "wrel.mm"
include "copab.mm"
include "relopab.mm"
include "eqid.mm"
include "dicval2.mm"
include "releqd.mm"
include "mpbiri.mm"
include "wss.mm"
include "ssrab2.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"
include "a1i.mm"
include "id.mm"
include "vex.mm"
include "dicopelval2.mm"
include "w3a.mm"
include "simprl.mm"
include "simpll.mm"
include "simprr.mm"
include "simpl.mm"
include "lhpocnel2.mm"
include "adantr.mm"
include "simpr.mm"
include "ltrniotacl.mm"
include "syl3anc.mm"
include "tendocl.mm"
include "eqeltrd.mm"
include "3jca.mm"
include "simpr3.mm"
include "simpr2.mm"
include "jca.mm"
include "impbida.mm"
include "dvhbase.mm"
include "rexeqdv.mm"
include "ccom.mm"
include "tendoidcl.mm"
include "ad2antrr.mm"
include "dvhopvsca.mm"
include "syl13anc.mm"
include "eqeq2d.mm"
include "opth.mm"
include "syl6bb.mm"
include "tendo1mulr.mm"
include "adantlr.mm"
include "equcom.mm"
include "anbi2d.mm"
include "bitrd.mm"
include "ancom.mm"
include "rexbidva.mm"
include "3anbi3d.mm"
include "fveq1.mm"
include "ceqsrexv.mm"
include "pm5.32i.mm"
include "anbi2i.mm"
include "3anass.mm"
include "3bitr4i.mm"
include "syl6rbb.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "rabxp.mm"
include "eleq2i.mm"
include "opabid.mm"
include "bitr2i.mm"
include "eqrelrdv2.mm"
include "syl21anc.mm"
include "wi.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "dvhvscacl.mm"
include "syl12anc.mm"
include "eleq1a.mm"
include "syl.mm"
include "rexlimdva.mm"
include "pm4.71rd.mm"
include "abbidv.mm"
include "3eqtr4a.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "dvhelvbasei.mm"
include "lspsn.mm"
include "eqtr4d.mm"

theorem diclspsn
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cW: class W
  let vg: setvar g
  let vs: setvar s
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume diclspsn.l: |- .<_ = ( le ` K )
  assume diclspsn.a: |- A = ( Atoms ` K )
  assume diclspsn.h: |- H = ( LHyp ` K )
  assume diclspsn.p: |- P = ( ( oc ` K ) ` W )
  assume diclspsn.t: |- T = ( ( LTrn ` K ) ` W )
  assume diclspsn.i: |- I = ( ( DIsoC ` K ) ` W )
  assume diclspsn.u: |- U = ( ( DVecH ` K ) ` W )
  assume diclspsn.n: |- N = ( LSpan ` U )
  assume diclspsn.f: |- F = ( iota_ f e. T ( f ` P ) = Q )

  disjoint .<_ f
  disjoint P f
  disjoint A f
  disjoint H f
  disjoint T f
  disjoint K f
  disjoint Q f
  disjoint W f
  disjoint f g
  disjoint f s
  disjoint f v
  disjoint f x
  disjoint g s
  disjoint g v
  disjoint g x
  disjoint .<_ g
  disjoint s v
  disjoint s x
  disjoint .<_ s
  disjoint v x
  disjoint .<_ v
  disjoint .<_ x
  disjoint F g
  disjoint F s
  disjoint F v
  disjoint F x
  disjoint I g
  disjoint I s
  disjoint N v
  disjoint N x
  disjoint f y
  disjoint P y
  disjoint A g
  disjoint A s
  disjoint A v
  disjoint A x
  disjoint H g
  disjoint H s
  disjoint H v
  disjoint H x
  disjoint g y
  disjoint T g
  disjoint s y
  disjoint T s
  disjoint v y
  disjoint T v
  disjoint x y
  disjoint T x
  disjoint T y
  disjoint U g
  disjoint U s
  disjoint U v
  disjoint U x
  disjoint f z
  disjoint g z
  disjoint K g
  disjoint s z
  disjoint K s
  disjoint v z
  disjoint K v
  disjoint x z
  disjoint K x
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint Q g
  disjoint Q s
  disjoint Q v
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint W g
  disjoint W s
  disjoint W v
  disjoint W x
  disjoint W y
  disjoint W z
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( I ` Q ) = ( N ` { <. F , ( _I |` T ) >. } ) )

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
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    wa
    #
    cQ
    cI
    cfv
    #
    vv
    cv
    #
    vx
    cv
    #
    cF
    cid
    cT
    cres
    #
    cop
    #
    cU
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vx
    cU
    csca
    cfv
    #
    cbs
    cfv
    #
    wrex
    #
    vv
    cab
    #
    @7
    csn
    cN
    cfv
    #
    @2
    @13
    vv
    cT
    cW
    cK
    ctendo
    cfv
    cfv
    #
    cxp
    #
    crab
    #
    @4
    @17
    wcel
    #
    @13
    wa
    #
    vv
    cab
    @3
    @14
    @13
    vv
    @17
    df-rab
    @2
    @3
    wrel
    #
    @18
    wrel
    #
    @2
    @3
    @18
    wceq
    @2
    @21
    vy
    cv
    cF
    vz
    cv
    #
    cfv
    wceq
    @23
    @16
    wcel
    wa
    #
    vy
    vz
    copab
    #
    wrel
    @24
    vy
    vz
    relopab
    @2
    @3
    @25
    cA
    cP
    cQ
    cT
    vy
    vf
    @16
    cF
    cH
    cI
    cK
    c.le
    chlt
    cW
    vz
    diclspsn.l
    diclspsn.a
    diclspsn.h
    diclspsn.p
    diclspsn.t
    @16
    eqid
    #
    diclspsn.i
    diclspsn.f
    dicval2
    releqd
    mpbiri
    @22
    @2
    @18
    @17
    wss
    @17
    wrel
    @22
    @13
    vv
    @17
    ssrab2
    cT
    @16
    relxp
    @18
    @17
    relss
    mp2
    a1i
    @2
    id
    @2
    vg
    vs
    @3
    @18
    @2
    vg
    cv
    #
    vs
    cv
    #
    cop
    #
    @3
    wcel
    @27
    cF
    @28
    cfv
    #
    wceq
    #
    @28
    @16
    wcel
    #
    wa
    #
    @29
    @18
    wcel
    #
    cA
    cP
    cQ
    @28
    cT
    vf
    @16
    @27
    cF
    cH
    cI
    cK
    c.le
    chlt
    cW
    diclspsn.l
    diclspsn.a
    diclspsn.h
    diclspsn.p
    diclspsn.t
    @26
    diclspsn.i
    diclspsn.f
    vg
    vex
    #
    vs
    vex
    #
    dicopelval2
    @2
    @33
    @27
    cT
    wcel
    #
    @32
    @29
    @9
    wceq
    #
    vx
    @12
    wrex
    #
    w3a
    #
    @34
    @2
    @33
    @37
    @32
    @31
    w3a
    #
    @40
    @2
    @33
    @41
    @2
    @33
    wa
    #
    @37
    @32
    @31
    @42
    @27
    @30
    cT
    @2
    @31
    @32
    simprl
    #
    @42
    @0
    @32
    cF
    cT
    wcel
    #
    @30
    cT
    wcel
    @0
    @1
    @33
    simpll
    @2
    @31
    @32
    simprr
    #
    @2
    @44
    @33
    @2
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
    @1
    @44
    @0
    @1
    simpl
    #
    @0
    @46
    @1
    cA
    cP
    cH
    cK
    c.le
    cW
    diclspsn.l
    diclspsn.a
    diclspsn.h
    diclspsn.p
    lhpocnel2
    adantr
    @0
    @1
    simpr
    cA
    cP
    cQ
    cT
    vf
    cF
    cH
    cK
    c.le
    cW
    diclspsn.l
    diclspsn.a
    diclspsn.h
    diclspsn.t
    diclspsn.f
    ltrniotacl
    syl3anc
    #
    adantr
    @28
    cT
    @16
    cF
    cH
    cK
    chlt
    cW
    diclspsn.h
    diclspsn.t
    @26
    tendocl
    syl3anc
    eqeltrd
    @45
    @43
    3jca
    @2
    @41
    wa
    @31
    @32
    @2
    @37
    @32
    @31
    simpr3
    @2
    @37
    @32
    @31
    simpr2
    jca
    impbida
    @2
    @40
    @37
    @32
    @5
    @28
    wceq
    #
    @27
    cF
    @5
    cfv
    #
    wceq
    #
    wa
    #
    vx
    @16
    wrex
    #
    w3a
    #
    @41
    @2
    @39
    @53
    @37
    @32
    @2
    @39
    @38
    vx
    @16
    wrex
    @53
    @2
    @38
    vx
    @12
    @16
    @0
    @12
    @16
    wceq
    @1
    @12
    cU
    @16
    @11
    cH
    cK
    cW
    chlt
    diclspsn.h
    @26
    diclspsn.u
    @11
    eqid
    #
    @12
    eqid
    #
    dvhbase
    adantr
    #
    rexeqdv
    @2
    @38
    @52
    vx
    @16
    @2
    @5
    @16
    wcel
    #
    wa
    #
    @38
    @51
    @49
    wa
    #
    @52
    @59
    @38
    @51
    @28
    @5
    @6
    ccom
    #
    wceq
    #
    wa
    #
    @60
    @59
    @38
    @29
    @50
    @61
    cop
    #
    wceq
    @63
    @59
    @9
    @64
    @29
    @59
    @0
    @58
    @44
    @6
    @16
    wcel
    #
    @9
    @64
    wceq
    @0
    @1
    @58
    simpll
    @2
    @58
    simpr
    @2
    @44
    @58
    @48
    adantr
    @0
    @65
    @1
    @58
    cT
    @16
    cH
    cK
    cW
    diclspsn.h
    diclspsn.t
    @26
    tendoidcl
    #
    ad2antrr
    @5
    cT
    @8
    cU
    @16
    cF
    cH
    cK
    chlt
    cW
    @6
    diclspsn.h
    diclspsn.t
    @26
    diclspsn.u
    @8
    eqid
    #
    dvhopvsca
    syl13anc
    eqeq2d
    @27
    @28
    @50
    @61
    @35
    @36
    opth
    syl6bb
    @59
    @62
    @49
    @51
    @59
    @62
    @28
    @5
    wceq
    @49
    @59
    @61
    @5
    @28
    @0
    @58
    @61
    @5
    wceq
    @1
    cT
    @5
    @16
    cH
    cK
    cW
    diclspsn.h
    diclspsn.t
    @26
    tendo1mulr
    adantlr
    eqeq2d
    vs
    vx
    equcom
    syl6bb
    anbi2d
    bitrd
    @51
    @49
    ancom
    syl6bb
    rexbidva
    bitrd
    3anbi3d
    @37
    @32
    @53
    wa
    #
    wa
    @37
    @32
    @31
    wa
    #
    wa
    @54
    @41
    @68
    @69
    @37
    @32
    @53
    @31
    @51
    @31
    vx
    @28
    @16
    @49
    @50
    @30
    @27
    cF
    @5
    @28
    fveq1
    eqeq2d
    ceqsrexv
    pm5.32i
    anbi2i
    @37
    @32
    @53
    3anass
    @37
    @32
    @31
    3anass
    3bitr4i
    syl6rbb
    bitrd
    @34
    @29
    @40
    vg
    vs
    copab
    #
    wcel
    @40
    @18
    @70
    @29
    @13
    @39
    vv
    vg
    vs
    cT
    @16
    @4
    @29
    wceq
    @10
    @38
    vx
    @12
    @4
    @29
    @9
    eqeq1
    rexbidv
    rabxp
    eleq2i
    @40
    vg
    vs
    opabid
    bitr2i
    syl6bb
    bitrd
    eqrelrdv2
    syl21anc
    @2
    @13
    @20
    vv
    @2
    @13
    @19
    @2
    @10
    @19
    vx
    @12
    @2
    @5
    @12
    wcel
    #
    wa
    #
    @9
    @17
    wcel
    #
    @10
    @19
    wi
    @72
    @0
    @58
    @7
    @17
    wcel
    #
    @73
    @0
    @1
    @71
    simpll
    @2
    @71
    @58
    @2
    @12
    @16
    @5
    @57
    eleq2d
    biimpa
    @2
    @74
    @71
    @2
    @44
    @65
    @74
    @48
    @0
    @65
    @1
    @66
    adantr
    #
    cF
    @6
    cT
    @16
    opelxpi
    syl2anc
    adantr
    @5
    cT
    @8
    cU
    @16
    @7
    cH
    cK
    cW
    diclspsn.h
    diclspsn.t
    @26
    diclspsn.u
    @67
    dvhvscacl
    syl12anc
    @9
    @17
    @4
    eleq1a
    syl
    rexlimdva
    pm4.71rd
    abbidv
    3eqtr4a
    @2
    cU
    clmod
    wcel
    @7
    cU
    cbs
    cfv
    #
    wcel
    #
    @15
    @14
    wceq
    @2
    cU
    cH
    cK
    cW
    diclspsn.h
    diclspsn.u
    @47
    dvhlmod
    @2
    @0
    @44
    @65
    @77
    @47
    @48
    @75
    @6
    cT
    cU
    @16
    cF
    cH
    cK
    @76
    cW
    chlt
    diclspsn.h
    diclspsn.t
    @26
    diclspsn.u
    @76
    eqid
    #
    dvhelvbasei
    syl12anc
    vv
    @8
    vx
    @11
    @12
    cN
    @76
    cU
    @7
    @55
    @56
    @78
    @67
    diclspsn.n
    lspsn
    syl2anc
    eqtr4d
end
