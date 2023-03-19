include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "cn0.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cdecpmat.mm"
include "cv.mm"
include "cco1.mm"
include "cmpt2.mm"
include "wceq.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt.mm"
include "cbs.mm"
include "crg.mm"
include "simpll.mm"
include "crngring.mm"
include "ply1ring.mm"
include "syl.mm"
include "ad2antlr.mm"
include "adantl.mm"
include "simp2.mm"
include "cmgp.mm"
include "eqid.mm"
include "ply1moncl.mm"
include "syl2an.mm"
include "anim2i.mm"
include "simp1.mm"
include "anim12i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "mat2pmatbas.mm"
include "jca.mm"
include "matvscl.mm"
include "syl21anc.mm"
include "simpr3.mm"
include "decpmatval.mm"
include "syl2anc.mm"
include "cmulr.mm"
include "cvsca.mm"
include "3ad2ant1.mm"
include "3simpc.mm"
include "matvscacell.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "cascl.mm"
include "mat2pmatvalel.mm"
include "oveq2d.mm"
include "casa.mm"
include "csca.mm"
include "ply1assa.mm"
include "simp3.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "matecld.mm"
include "ply1sca.mm"
include "eqcomd.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "asclmul2.mm"
include "eqtrd.mm"
include "simp1r2.mm"
include "coe1tm.mm"
include "3eqtrd.mm"
include "mpt2eq3dva.mm"
include "wral.mm"
include "cvv.mm"
include "mat0op.mm"
include "syl5eq.mm"
include "weq.mm"
include "eqidd.mm"
include "simprl.mm"
include "simprr.mm"
include "fvexd.mm"
include "ovmpt2d.mm"
include "ifeq2d.mm"
include "oveq12.mm"
include "ifeq1d.mm"
include "mpteq2dv.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "ovex.mm"
include "fvex.mm"
include "ifex.mm"
include "a1i.mm"
include "fvmptd.mm"
include "sylan9eqr.mm"
include "ifov.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "wb.mm"
include "simplr.mm"
include "ring0cl.mm"
include "ifcld.mm"
include "eqeltrd.mm"
include "matbas2d.mm"
include "matring.mm"
include "3syl.mm"
include "eqmat.mm"
include "mpbird.mm"

theorem monmatcollpw
  let cA: class A
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let c.ex: class .^
  let cI: class I
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  let vl: setvar l
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  assume monmatcollpw.p: |- P = ( Poly1 ` R )
  assume monmatcollpw.c: |- C = ( N Mat P )
  assume monmatcollpw.a: |- A = ( N Mat R )
  assume monmatcollpw.k: |- K = ( Base ` A )
  assume monmatcollpw.0: |- .0. = ( 0g ` A )
  assume monmatcollpw.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume monmatcollpw.x: |- X = ( var1 ` R )
  assume monmatcollpw.m: |- .x. = ( .s ` C )
  assume monmatcollpw.t: |- T = ( N matToPolyMat R )


  assert |- ( ( ( N e. Fin /\ R e. CRing ) /\ ( M e. K /\ L e. NN0 /\ I e. NN0 ) ) -> ( ( ( L .^ X ) .x. ( T ` M ) ) decompPMat I ) = if ( I = L , M , .0. ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    wa
    #
    cM
    cK
    wcel
    #
    cL
    cn0
    wcel
    #
    cI
    cn0
    wcel
    #
    w3a
    #
    wa
    #
    cL
    cX
    c.ex
    co
    #
    cM
    cT
    cfv
    #
    c.x
    co
    #
    cI
    cdecpmat
    co
    #
    vi
    vj
    cN
    cN
    cI
    vi
    cv
    #
    vj
    cv
    #
    @10
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cmpt2
    #
    vi
    vj
    cN
    cN
    cI
    vl
    cn0
    vl
    cv
    #
    cL
    wceq
    #
    @12
    @13
    cM
    co
    #
    cR
    c0g
    cfv
    #
    cif
    #
    cmpt
    #
    cfv
    #
    cmpt2
    #
    cI
    cL
    wceq
    #
    cM
    c.0
    cif
    #
    @7
    @10
    cC
    cbs
    cfv
    #
    wcel
    #
    @5
    @11
    @17
    wceq
    @7
    @0
    cP
    crg
    wcel
    #
    @8
    cP
    cbs
    cfv
    #
    wcel
    #
    @9
    @28
    wcel
    #
    wa
    #
    @29
    @0
    @1
    @6
    simpll
    #
    @1
    @30
    @0
    @6
    @1
    cR
    crg
    wcel
    #
    @30
    cR
    crngring
    #
    cP
    cR
    monmatcollpw.p
    ply1ring
    syl
    ad2antlr
    #
    @7
    @32
    @33
    @2
    @36
    @4
    @32
    @6
    @1
    @36
    @0
    @37
    adantl
    #
    @3
    @4
    @5
    simp2
    @31
    cL
    cP
    cR
    c.ex
    cP
    cmgp
    cfv
    #
    cX
    monmatcollpw.p
    monmatcollpw.x
    @40
    eqid
    #
    monmatcollpw.e
    @31
    eqid
    #
    ply1moncl
    syl2an
    #
    @7
    @0
    @36
    @3
    w3a
    #
    @33
    @7
    @0
    @36
    wa
    #
    @3
    wa
    @44
    @2
    @45
    @6
    @3
    @1
    @36
    @0
    @37
    anim2i
    #
    @3
    @4
    @5
    simp1
    #
    anim12i
    @0
    @36
    @3
    df-3an
    sylibr
    cA
    cK
    cC
    cP
    cR
    cT
    cM
    cN
    monmatcollpw.t
    monmatcollpw.a
    monmatcollpw.k
    monmatcollpw.p
    monmatcollpw.c
    mat2pmatbas
    syl
    jca
    #
    cC
    @28
    @8
    cP
    c.x
    @31
    cN
    @9
    @42
    monmatcollpw.c
    @28
    eqid
    #
    monmatcollpw.m
    matvscl
    syl21anc
    @2
    @3
    @4
    @5
    simpr3
    #
    cC
    @28
    cP
    vi
    vj
    cI
    @10
    cN
    monmatcollpw.c
    @49
    decpmatval
    syl2anc
    @7
    vi
    vj
    cN
    cN
    @16
    @24
    @7
    @12
    cN
    wcel
    #
    @13
    cN
    wcel
    #
    w3a
    #
    @16
    cI
    @8
    @12
    @13
    @9
    co
    #
    cP
    cmulr
    cfv
    #
    co
    #
    cco1
    cfv
    #
    cfv
    cI
    @20
    @8
    cP
    cvsca
    cfv
    #
    co
    #
    cco1
    cfv
    #
    cfv
    @24
    @53
    cI
    @15
    @57
    @53
    @14
    @56
    cco1
    @53
    @30
    @34
    @51
    @52
    wa
    #
    @14
    @56
    wceq
    @7
    @51
    @30
    @52
    @38
    3ad2ant1
    @7
    @51
    @34
    @52
    @48
    3ad2ant1
    @7
    @51
    @52
    3simpc
    #
    cC
    @28
    cP
    c.x
    @55
    @12
    @13
    @31
    cN
    @8
    @9
    monmatcollpw.c
    @49
    @42
    monmatcollpw.m
    @55
    eqid
    #
    matvscacell
    syl3anc
    fveq2d
    fveq1d
    @53
    cI
    @57
    @60
    @53
    @56
    @59
    cco1
    @53
    @56
    @8
    @20
    cP
    cascl
    cfv
    #
    cfv
    #
    @55
    co
    #
    @59
    @53
    @54
    @65
    @8
    @55
    @53
    @0
    @1
    @3
    w3a
    #
    @61
    @54
    @65
    wceq
    @7
    @51
    @67
    @52
    @7
    @2
    @3
    wa
    @67
    @6
    @3
    @2
    @47
    anim2i
    @0
    @1
    @3
    df-3an
    sylibr
    3ad2ant1
    @62
    cA
    cK
    cP
    cR
    @64
    cT
    cM
    cN
    ccrg
    @12
    @13
    monmatcollpw.t
    monmatcollpw.a
    monmatcollpw.k
    monmatcollpw.p
    @64
    eqid
    #
    mat2pmatvalel
    syl2anc
    oveq2d
    @53
    cP
    casa
    wcel
    #
    @20
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    @32
    @66
    @59
    wceq
    @7
    @51
    @69
    @52
    @1
    @69
    @0
    @6
    cP
    cR
    monmatcollpw.p
    ply1assa
    ad2antlr
    3ad2ant1
    @53
    @20
    cR
    cbs
    cfv
    #
    @71
    @53
    cA
    cA
    cbs
    cfv
    #
    cR
    @12
    @13
    @72
    cM
    cN
    monmatcollpw.a
    @72
    eqid
    #
    @73
    eqid
    @7
    @51
    @52
    simp2
    @7
    @51
    @52
    simp3
    @7
    @51
    cM
    @73
    wcel
    #
    @52
    @6
    @75
    @2
    @3
    @4
    @75
    @5
    @3
    @75
    cK
    @73
    cM
    monmatcollpw.k
    eleq2i
    #
    biimpi
    3ad2ant1
    adantl
    #
    3ad2ant1
    matecld
    #
    @7
    @51
    @71
    @72
    wceq
    #
    @52
    @2
    @79
    @6
    @2
    @70
    cR
    cbs
    @2
    cR
    @70
    @1
    cR
    @70
    wceq
    @0
    cP
    cR
    ccrg
    monmatcollpw.p
    ply1sca
    adantl
    eqcomd
    fveq2d
    adantr
    3ad2ant1
    eleqtrrd
    @7
    @51
    @32
    @52
    @43
    3ad2ant1
    @64
    @20
    @58
    @55
    @70
    @71
    @31
    cP
    @8
    @68
    @70
    eqid
    @71
    eqid
    @42
    @63
    @58
    eqid
    #
    asclmul2
    syl3anc
    eqtrd
    fveq2d
    fveq1d
    @53
    cI
    @60
    @23
    @53
    @36
    @20
    @72
    wcel
    @4
    @60
    @23
    wceq
    @7
    @51
    @36
    @52
    @1
    @36
    @0
    @6
    @37
    ad2antlr
    3ad2ant1
    @78
    @3
    @4
    @5
    @2
    @51
    @52
    simp1r2
    vl
    @20
    cL
    cP
    cR
    @58
    c.ex
    @72
    @40
    cX
    @21
    @21
    eqid
    #
    @74
    monmatcollpw.p
    monmatcollpw.x
    @80
    @41
    monmatcollpw.e
    coe1tm
    syl3anc
    fveq1d
    3eqtrd
    mpt2eq3dva
    @7
    @25
    @27
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    @25
    co
    #
    @83
    @84
    @27
    co
    #
    wceq
    #
    vy
    cN
    wral
    vx
    cN
    wral
    #
    @7
    @87
    vx
    vy
    cN
    cN
    @7
    @83
    cN
    wcel
    #
    @84
    cN
    wcel
    #
    wa
    #
    wa
    #
    @26
    @83
    @84
    cM
    co
    #
    @21
    cif
    #
    @26
    @93
    @83
    @84
    c.0
    co
    #
    cif
    #
    @85
    @86
    @92
    @26
    @21
    @95
    @93
    @92
    @95
    @21
    @92
    vz
    vw
    @83
    @84
    cN
    cN
    @21
    @21
    c.0
    cvv
    @92
    c.0
    cA
    c0g
    cfv
    #
    vz
    vw
    cN
    cN
    @21
    cmpt2
    #
    monmatcollpw.0
    @92
    @45
    @97
    @98
    wceq
    @7
    @45
    @91
    @2
    @45
    @6
    @46
    adantr
    adantr
    cA
    cR
    vz
    vw
    cN
    @21
    monmatcollpw.a
    @81
    mat0op
    syl
    syl5eq
    @92
    vz
    vx
    weq
    vw
    vy
    weq
    wa
    wa
    @21
    eqidd
    @7
    @89
    @90
    simprl
    #
    @7
    @89
    @90
    simprr
    #
    @92
    cR
    c0g
    fvexd
    ovmpt2d
    eqcomd
    ifeq2d
    @92
    vi
    vj
    @83
    @84
    cN
    cN
    @24
    @94
    @25
    cvv
    @92
    @25
    eqidd
    vi
    vx
    weq
    vj
    vy
    weq
    wa
    #
    @92
    @24
    cI
    vl
    cn0
    @19
    @93
    @21
    cif
    #
    cmpt
    #
    cfv
    @94
    @101
    cI
    @23
    @103
    @101
    vl
    cn0
    @22
    @102
    @101
    @19
    @20
    @93
    @21
    @12
    @83
    @13
    @84
    cM
    oveq12
    ifeq1d
    mpteq2dv
    fveq1d
    @92
    vl
    cI
    @102
    @94
    cn0
    @103
    cvv
    @92
    @103
    eqidd
    @18
    cI
    wceq
    #
    @102
    @94
    wceq
    @92
    @104
    @19
    @26
    @93
    @21
    @18
    cI
    cL
    eqeq1
    #
    ifbid
    adantl
    @7
    @5
    @91
    @50
    adantr
    @94
    cvv
    wcel
    @92
    @26
    @93
    @21
    @83
    @84
    cM
    ovex
    cR
    c0g
    fvex
    ifex
    a1i
    #
    fvmptd
    sylan9eqr
    @99
    @100
    @106
    ovmpt2d
    @86
    @96
    wceq
    @92
    @26
    @83
    @84
    cM
    c.0
    ifov
    a1i
    3eqtr4d
    ralrimivva
    @7
    @25
    cK
    wcel
    @27
    cK
    wcel
    @82
    @88
    wb
    @7
    vi
    vj
    cA
    cK
    @24
    cR
    @72
    cN
    ccrg
    monmatcollpw.a
    @74
    monmatcollpw.k
    @35
    @0
    @1
    @6
    simplr
    @53
    @24
    @26
    @20
    @21
    cif
    #
    @72
    @53
    vl
    cI
    @22
    @107
    cn0
    @23
    @72
    @53
    @23
    eqidd
    @104
    @22
    @107
    wceq
    @53
    @104
    @19
    @26
    @20
    @21
    @105
    ifbid
    adantl
    @7
    @51
    @5
    @52
    @50
    3ad2ant1
    @53
    @26
    @20
    @21
    @72
    @78
    @7
    @51
    @21
    @72
    wcel
    #
    @52
    @2
    @108
    @6
    @2
    @36
    @108
    @39
    @72
    cR
    @21
    @74
    @81
    ring0cl
    syl
    adantr
    3ad2ant1
    ifcld
    #
    fvmptd
    @109
    eqeltrd
    matbas2d
    @7
    @26
    cM
    c.0
    cK
    @7
    @75
    @3
    @77
    @76
    sylibr
    @2
    c.0
    cK
    wcel
    #
    @6
    @2
    @45
    cA
    crg
    wcel
    @110
    @46
    cA
    cR
    cN
    monmatcollpw.a
    matring
    cK
    cA
    c.0
    monmatcollpw.k
    monmatcollpw.0
    ring0cl
    3syl
    adantr
    ifcld
    cA
    cK
    cR
    vx
    vy
    cN
    @25
    @27
    monmatcollpw.a
    monmatcollpw.k
    eqmat
    syl2anc
    mpbird
    3eqtrd
end
