include "cdm.mm"
include "cv.mm"
include "csb.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "c2nd.mm"
include "cfv.mm"
include "c1st.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfcsb.mm"
include "csbeq1a.mm"
include "weq.mm"
include "sylan9eqr.mm"
include "cbvmpt2x2.mm"
include "cop.mm"
include "wceq.mm"
include "vex.mm"
include "op2ndd.mm"
include "csbeq1d.mm"
include "op1std.mm"
include "csbeq2dv.mm"
include "eqtrd.mm"
include "mpt2mptx2.mm"
include "3eqtr4i.mm"
include "dmmptss.mm"
include "nfxp.mm"
include "sneq.mm"
include "xpeq12d.mm"
include "cbviun.mm"
include "sseqtr4i.mm"

theorem dmmpt2ssx2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vk: setvar k
  assume dmmpt2ssx2.1: |- F = ( x e. A , y e. B |-> C )

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint A t
  disjoint u v
  disjoint u x
  disjoint A u
  disjoint v x
  disjoint A v
  disjoint t y
  disjoint B t
  disjoint u y
  disjoint B u
  disjoint v y
  disjoint B v
  disjoint C t
  disjoint C u
  disjoint C v
  disjoint k x
  assert |- dom F C_ U_ y e. B ( A X. { y } )

  proof
    cF
    cdm
    vu
    cB
    vy
    vu
    cv
    #
    cA
    csb
    #
    @0
    csn
    #
    cxp
    #
    ciun
    #
    vy
    cB
    cA
    vy
    cv
    #
    csn
    #
    cxp
    #
    ciun
    vt
    @4
    vy
    vt
    cv
    #
    c2nd
    cfv
    #
    vx
    @8
    c1st
    cfv
    #
    cC
    csb
    #
    csb
    #
    cF
    vx
    vy
    cA
    cB
    cC
    cmpt2
    vv
    vu
    @1
    cB
    vy
    @0
    vx
    vv
    cv
    #
    cC
    csb
    #
    csb
    #
    cmpt2
    cF
    vt
    @4
    @12
    cmpt
    vx
    vy
    vu
    vv
    cA
    cB
    cC
    @1
    @15
    vu
    cA
    nfcv
    vy
    @0
    cA
    nfcsb1v
    #
    vu
    cC
    nfcv
    vv
    cC
    nfcv
    vx
    vy
    @0
    @14
    vx
    @0
    nfcv
    vx
    @13
    cC
    nfcsb1v
    nfcsb
    vy
    @0
    @14
    nfcsb1v
    vy
    @0
    cA
    csbeq1a
    #
    vx
    vv
    weq
    vy
    vu
    weq
    #
    cC
    @14
    @15
    vx
    @13
    cC
    csbeq1a
    vy
    @0
    @14
    csbeq1a
    sylan9eqr
    cbvmpt2x2
    dmmpt2ssx2.1
    vv
    vu
    vt
    @1
    cB
    @12
    @15
    @8
    @13
    @0
    cop
    wceq
    #
    @12
    vy
    @0
    @11
    csb
    @15
    @19
    vy
    @9
    @0
    @11
    @13
    @0
    @8
    vv
    vex
    #
    vu
    vex
    #
    op2ndd
    csbeq1d
    @19
    vy
    @0
    @11
    @14
    @19
    vx
    @10
    @13
    cC
    @13
    @0
    @8
    @20
    @21
    op1std
    csbeq1d
    csbeq2dv
    eqtrd
    mpt2mptx2
    3eqtr4i
    dmmptss
    vy
    vu
    cB
    @7
    @3
    vu
    @7
    nfcv
    vy
    @1
    @2
    @16
    vy
    @2
    nfcv
    nfxp
    @18
    cA
    @1
    @6
    @2
    @17
    @5
    @0
    sneq
    xpeq12d
    cbviun
    sseqtr4i
end
