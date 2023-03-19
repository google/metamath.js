include "crg.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "c1o.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "cif.mm"
include "cbs.mm"
include "eqid.mm"
include "ply1tmcl.mm"
include "coe1fval2.mm"
include "syl.mm"
include "cmap.mm"
include "wf.mm"
include "fconst6g.mm"
include "nn0ex.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "elmap.mm"
include "sylibr.mm"
include "adantl.mm"
include "eqidd.mm"
include "cmvr.mm"
include "cmpl.mm"
include "cmgp.mm"
include "cmg.mm"
include "cur.mm"
include "cvv.mm"
include "mgpbas.mm"
include "a1i.mm"
include "cps1.mm"
include "ply1bas.mm"
include "wss.mm"
include "ssv.mm"
include "wa.mm"
include "cplusg.mm"
include "ovexd.mm"
include "cmulr.mm"
include "mgpplusg.mm"
include "ply1mulr.mm"
include "eqtr3i.mm"
include "oveqdr.mm"
include "mulgpropd.mm"
include "3ad2ant1.mm"
include "vr1val.mm"
include "oveq123d.mm"
include "oveq2d.mm"
include "psr1baslem.mm"
include "simp1.mm"
include "0lt1o.mm"
include "simp3.mm"
include "mplcoe3.mm"
include "ply1vsca.mm"
include "elsni.mm"
include "df1o2.mm"
include "eleq2s.mm"
include "iftrued.mm"
include "mpteq2dva.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"
include "3ad2ant3.mm"
include "eqeltrd.mm"
include "simp2.mm"
include "mplmon2.mm"
include "3eqtr2d.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "fmptco.mm"
include "adantr.mm"
include "eqeq2d.mm"
include "fveq1.mm"
include "vex.mm"
include "fvconst2.mm"
include "mp1i.mm"
include "simpl3.mm"
include "fvconst2g.mm"
include "sylancl.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "impbid1.mm"
include "bitrd.mm"
include "3eqtrd.mm"

theorem coe1tm
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let c.ex: class .^
  let cK: class K
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let cF: class F
  let cA: class A
  let cY: class Y
  let wph: wff ph
  let c.xp: class .X.
  let c.xb: class .xb
  assume coe1tm.z: |- .0. = ( 0g ` R )
  assume coe1tm.k: |- K = ( Base ` R )
  assume coe1tm.p: |- P = ( Poly1 ` R )
  assume coe1tm.x: |- X = ( var1 ` R )
  assume coe1tm.m: |- .x. = ( .s ` P )
  assume coe1tm.n: |- N = ( mulGrp ` P )
  assume coe1tm.e: |- .^ = ( .g ` N )

  disjoint .0. x
  disjoint C x
  disjoint D x
  disjoint K x
  disjoint .^ x
  disjoint N x
  disjoint P x
  disjoint X x
  disjoint R x
  disjoint .x. x
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint .0. a
  disjoint b x
  disjoint b y
  disjoint .0. b
  disjoint x y
  disjoint .0. y
  disjoint C b
  disjoint C y
  disjoint D a
  disjoint D b
  disjoint D y
  disjoint F x
  disjoint K b
  disjoint K y
  disjoint .^ y
  disjoint A x
  disjoint A y
  disjoint N y
  disjoint P y
  disjoint X y
  disjoint Y x
  disjoint ph x
  disjoint ph y
  disjoint R a
  disjoint R b
  disjoint R y
  disjoint .x. y
  disjoint .X. x
  disjoint .X. y
  disjoint .xb x
  assert |- ( ( R e. Ring /\ C e. K /\ D e. NN0 ) -> ( coe1 ` ( C .x. ( D .^ X ) ) ) = ( x e. NN0 |-> if ( x = D , C , .0. ) ) )

  proof
    cR
    crg
    wcel
    #
    cC
    cK
    wcel
    #
    cD
    cn0
    wcel
    #
    w3a
    #
    cC
    cD
    cX
    c.ex
    co
    #
    c.x
    co
    #
    cco1
    cfv
    #
    @5
    vx
    cn0
    c1o
    vx
    cv
    #
    csn
    #
    cxp
    #
    cmpt
    #
    ccom
    #
    vx
    cn0
    @9
    vb
    c1o
    vb
    cv
    #
    c0
    wceq
    #
    cD
    cc0
    cif
    #
    cmpt
    #
    wceq
    #
    cC
    c.0
    cif
    #
    cmpt
    vx
    cn0
    @7
    cD
    wceq
    #
    cC
    c.0
    cif
    #
    cmpt
    @3
    @5
    cP
    cbs
    cfv
    #
    wcel
    @6
    @11
    wceq
    @20
    cC
    cD
    cP
    cR
    c.x
    c.ex
    cK
    cN
    cX
    coe1tm.k
    coe1tm.p
    coe1tm.x
    coe1tm.m
    coe1tm.n
    coe1tm.e
    @20
    eqid
    #
    ply1tmcl
    vx
    @6
    @20
    cP
    cR
    @5
    @10
    @6
    eqid
    @21
    coe1tm.p
    @10
    eqid
    coe1fval2
    syl
    @3
    vx
    vy
    cn0
    cn0
    c1o
    cmap
    co
    #
    @9
    vy
    cv
    #
    @15
    wceq
    #
    cC
    c.0
    cif
    #
    @17
    @10
    @5
    @7
    cn0
    wcel
    #
    @9
    @22
    wcel
    #
    @3
    @26
    c1o
    cn0
    @9
    wf
    @27
    c1o
    @7
    cn0
    fconst6g
    cn0
    c1o
    @9
    nn0ex
    c1o
    con0
    1on
    elexi
    #
    elmap
    sylibr
    adantl
    @3
    @10
    eqidd
    @3
    @5
    cC
    cD
    c0
    c1o
    cR
    cmvr
    co
    #
    cfv
    #
    c1o
    cR
    cmpl
    co
    #
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    c.x
    co
    cC
    vy
    @22
    @24
    cR
    cur
    cfv
    #
    c.0
    cif
    cmpt
    #
    c.x
    co
    vy
    @22
    @25
    cmpt
    @3
    @4
    @34
    cC
    c.x
    @3
    cD
    cD
    cX
    @30
    c.ex
    @33
    @0
    @1
    c.ex
    @33
    wceq
    @2
    @0
    vx
    vy
    @20
    c.ex
    @33
    cN
    @32
    cvv
    coe1tm.e
    @33
    eqid
    #
    @20
    cN
    cbs
    cfv
    wceq
    @0
    @20
    cP
    cN
    coe1tm.n
    @21
    mgpbas
    a1i
    @20
    @32
    cbs
    cfv
    wceq
    @0
    @20
    @31
    @32
    @32
    eqid
    #
    cP
    cR
    cR
    cps1
    cfv
    #
    @20
    coe1tm.p
    @39
    eqid
    @21
    ply1bas
    mgpbas
    a1i
    @20
    cvv
    wss
    @0
    @20
    ssv
    a1i
    @0
    @7
    cvv
    wcel
    @23
    cvv
    wcel
    wa
    #
    wa
    @7
    @23
    cN
    cplusg
    cfv
    #
    ovexd
    @0
    @40
    vx
    vy
    @41
    @32
    cplusg
    cfv
    #
    @41
    @42
    wceq
    @0
    cP
    cmulr
    cfv
    #
    @41
    @42
    cP
    @43
    cN
    coe1tm.n
    @43
    eqid
    #
    mgpplusg
    @31
    @43
    @32
    @38
    cR
    @31
    @43
    cP
    coe1tm.p
    @31
    eqid
    #
    @44
    ply1mulr
    mgpplusg
    eqtr3i
    a1i
    oveqdr
    mulgpropd
    3ad2ant1
    @3
    cD
    eqidd
    cX
    @30
    wceq
    @3
    cR
    cX
    coe1tm.x
    vr1val
    a1i
    oveq123d
    oveq2d
    @3
    @36
    @34
    cC
    c.x
    @3
    vy
    @22
    @31
    cR
    @35
    va
    vb
    @33
    @32
    c1o
    cD
    @29
    con0
    c0
    c.0
    @45
    va
    psr1baslem
    #
    coe1tm.z
    @35
    eqid
    #
    c1o
    con0
    wcel
    @3
    1on
    a1i
    #
    @38
    @37
    @29
    eqid
    @0
    @1
    @2
    simp1
    #
    c0
    c1o
    wcel
    #
    @3
    0lt1o
    a1i
    @0
    @1
    @2
    simp3
    mplcoe3
    oveq2d
    @3
    vy
    cK
    @22
    @31
    cR
    c.x
    @35
    va
    c1o
    @15
    con0
    cC
    c.0
    @45
    cR
    @31
    c.x
    cP
    coe1tm.p
    @45
    coe1tm.m
    ply1vsca
    @46
    @47
    coe1tm.z
    coe1tm.k
    @48
    @49
    @3
    @15
    c1o
    cD
    csn
    #
    cxp
    #
    @22
    @3
    @15
    vb
    c1o
    cD
    cmpt
    @52
    @3
    vb
    c1o
    @14
    cD
    @12
    c1o
    wcel
    #
    @14
    cD
    wceq
    @3
    @53
    @13
    cD
    cc0
    @13
    @12
    c0
    csn
    c1o
    @12
    c0
    elsni
    df1o2
    eleq2s
    iftrued
    adantl
    mpteq2dva
    vb
    c1o
    cD
    fconstmpt
    syl6eqr
    #
    @2
    @0
    @52
    @22
    wcel
    #
    @1
    @2
    c1o
    cn0
    @52
    wf
    @55
    c1o
    cD
    cn0
    fconst6g
    cn0
    c1o
    @52
    nn0ex
    @28
    elmap
    sylibr
    3ad2ant3
    eqeltrd
    @0
    @1
    @2
    simp2
    mplmon2
    3eqtr2d
    @23
    @9
    wceq
    @24
    @16
    cC
    c.0
    @23
    @9
    @15
    eqeq1
    ifbid
    fmptco
    @3
    vx
    cn0
    @17
    @19
    @3
    @26
    wa
    #
    @16
    @18
    cC
    c.0
    @56
    @16
    @9
    @52
    wceq
    #
    @18
    @56
    @15
    @52
    @9
    @3
    @15
    @52
    wceq
    @26
    @54
    adantr
    eqeq2d
    @56
    @57
    @18
    @57
    c0
    @9
    cfv
    #
    c0
    @52
    cfv
    #
    wceq
    @56
    @18
    c0
    @9
    @52
    fveq1
    @56
    @58
    @7
    @59
    cD
    @50
    @58
    @7
    wceq
    @56
    0lt1o
    c1o
    @7
    c0
    vx
    vex
    fvconst2
    mp1i
    @56
    @2
    @50
    @59
    cD
    wceq
    @0
    @1
    @2
    @26
    simpl3
    0lt1o
    c1o
    cD
    c0
    cn0
    fvconst2g
    sylancl
    eqeq12d
    syl5ib
    @18
    @8
    @51
    c1o
    @7
    cD
    sneq
    xpeq2d
    impbid1
    bitrd
    ifbid
    mpteq2dva
    3eqtrd
end
