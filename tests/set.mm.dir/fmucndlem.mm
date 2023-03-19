include "wfn.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "cmpt2.mm"
include "cxp.mm"
include "cima.mm"
include "crn.mm"
include "cres.mm"
include "df-ima.mm"
include "wceq.mm"
include "simpr.mm"
include "resmpt2.mm"
include "sylancom.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "cvv.mm"
include "wcel.mm"
include "wtru.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmpt.mm"
include "vex.mm"
include "op1std.mm"
include "fveq2d.mm"
include "op2ndd.mm"
include "opeq12d.mm"
include "mpt2mpt.mm"
include "eqcomi.mm"
include "rneqi.mm"
include "fvexd.mm"
include "fliftrel.mm"
include "trud.mm"
include "sseli.mm"
include "adantl.mm"
include "xpss.mm"
include "wb.mm"
include "wrex.mm"
include "fvelimab.mm"
include "anbi12d.mm"
include "eqid.mm"
include "opex.mm"
include "elrnmpt2.mm"
include "eqcom.mm"
include "fvex.mm"
include "opth2.mm"
include "bitri.mm"
include "2rexbii.mm"
include "reeanv.mm"
include "3bitri.mm"
include "syl6rbbr.mm"
include "opelxp.mm"
include "syl6bbr.mm"
include "adantr.mm"
include "1st2nd2.mm"
include "eleq1d.mm"
include "3bitr4d.mm"
include "eqrdav.mm"
include "eqtrd.mm"

theorem fmucndlem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cX: class X
  let vp: setvar p

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint X x
  disjoint X y
  disjoint p x
  disjoint p y
  disjoint A p
  disjoint F p
  disjoint X p
  assert |- ( ( F Fn X /\ A C_ X ) -> ( ( x e. X , y e. X |-> <. ( F ` x ) , ( F ` y ) >. ) " ( A X. A ) ) = ( ( F " A ) X. ( F " A ) ) )

  proof
    cF
    cX
    wfn
    #
    cA
    cX
    wss
    #
    wa
    #
    vx
    vy
    cX
    cX
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    cop
    #
    cmpt2
    #
    cA
    cA
    cxp
    #
    cima
    #
    vx
    vy
    cA
    cA
    @7
    cmpt2
    #
    crn
    #
    cF
    cA
    cima
    #
    @13
    cxp
    #
    @2
    @10
    @8
    @9
    cres
    #
    crn
    @12
    @8
    @9
    df-ima
    @2
    @15
    @11
    @0
    @1
    @1
    @15
    @11
    wceq
    @0
    @1
    simpr
    vx
    vy
    cX
    cX
    cA
    cA
    @7
    resmpt2
    sylancom
    rneqd
    syl5eq
    @2
    vp
    @12
    @14
    cvv
    cvv
    cxp
    #
    vp
    cv
    #
    @12
    wcel
    #
    @17
    @16
    wcel
    #
    @2
    @12
    @16
    @17
    @12
    @16
    wss
    wtru
    vp
    @17
    c1st
    cfv
    #
    cF
    cfv
    #
    @17
    c2nd
    cfv
    #
    cF
    cfv
    #
    cvv
    cvv
    @12
    @9
    @11
    vp
    @9
    @21
    @23
    cop
    #
    cmpt
    #
    @25
    @11
    vx
    vy
    vp
    cA
    cA
    @24
    @7
    @17
    @3
    @5
    cop
    wceq
    #
    @21
    @4
    @23
    @6
    @26
    @20
    @3
    cF
    @3
    @5
    @17
    vx
    vex
    #
    vy
    vex
    #
    op1std
    fveq2d
    @26
    @22
    @5
    cF
    @3
    @5
    @17
    @27
    @28
    op2ndd
    fveq2d
    opeq12d
    mpt2mpt
    eqcomi
    rneqi
    wtru
    @17
    @9
    wcel
    wa
    #
    @20
    cF
    fvexd
    @29
    @22
    cF
    fvexd
    fliftrel
    trud
    sseli
    adantl
    @17
    @14
    wcel
    #
    @19
    @2
    @14
    @16
    @17
    @13
    @13
    xpss
    sseli
    adantl
    @2
    @19
    wa
    #
    @20
    @22
    cop
    #
    @12
    wcel
    #
    @32
    @14
    wcel
    #
    @18
    @30
    @2
    @33
    @34
    wb
    @19
    @2
    @33
    @20
    @13
    wcel
    #
    @22
    @13
    wcel
    #
    wa
    #
    @34
    @2
    @37
    @4
    @20
    wceq
    #
    vx
    cA
    wrex
    #
    @6
    @22
    wceq
    #
    vy
    cA
    wrex
    #
    wa
    #
    @33
    @2
    @35
    @39
    @36
    @41
    vx
    cX
    cA
    @20
    cF
    fvelimab
    vy
    cX
    cA
    @22
    cF
    fvelimab
    anbi12d
    @33
    @32
    @7
    wceq
    #
    vy
    cA
    wrex
    vx
    cA
    wrex
    @38
    @40
    wa
    #
    vy
    cA
    wrex
    vx
    cA
    wrex
    @42
    vx
    vy
    cA
    cA
    @7
    @32
    @11
    @11
    eqid
    @4
    @6
    opex
    elrnmpt2
    @43
    @44
    vx
    vy
    cA
    cA
    @43
    @7
    @32
    wceq
    @44
    @32
    @7
    eqcom
    @4
    @6
    @20
    @22
    @17
    c1st
    fvex
    @17
    c2nd
    fvex
    opth2
    bitri
    2rexbii
    @38
    @40
    vx
    vy
    cA
    cA
    reeanv
    3bitri
    syl6rbbr
    @20
    @22
    @13
    @13
    opelxp
    syl6bbr
    adantr
    @31
    @17
    @32
    @12
    @19
    @17
    @32
    wceq
    @2
    @17
    cvv
    cvv
    1st2nd2
    adantl
    #
    eleq1d
    @31
    @17
    @32
    @14
    @45
    eleq1d
    3bitr4d
    eqrdav
    eqtrd
end
