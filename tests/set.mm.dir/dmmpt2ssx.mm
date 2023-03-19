include "cdm.mm"
include "cv.mm"
include "csn.mm"
include "csb.mm"
include "cxp.mm"
include "ciun.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfcsb.mm"
include "csbeq1a.mm"
include "wceq.mm"
include "sylan9eqr.mm"
include "cbvmpt2x.mm"
include "cop.mm"
include "vex.mm"
include "op1std.mm"
include "csbeq1d.mm"
include "op2ndd.mm"
include "csbeq2dv.mm"
include "eqtrd.mm"
include "mpt2mptx.mm"
include "3eqtr4i.mm"
include "dmmptss.mm"
include "nfxp.mm"
include "sneq.mm"
include "xpeq12d.mm"
include "cbviun.mm"
include "sseqtr4i.mm"

theorem dmmpt2ssx
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cD: class D
  assume fmpt2x.1: |- F = ( x e. A , y e. B |-> C )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B t
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B z
  disjoint C t
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C z
  disjoint D v
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  assert |- dom F C_ U_ x e. A ( { x } X. B )

  proof
    cF
    cdm
    vu
    cA
    vu
    cv
    #
    csn
    #
    vx
    @0
    cB
    csb
    #
    cxp
    #
    ciun
    #
    vx
    cA
    vx
    cv
    #
    csn
    #
    cB
    cxp
    #
    ciun
    vt
    @4
    vx
    vt
    cv
    #
    c1st
    cfv
    #
    vy
    @8
    c2nd
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
    vu
    vv
    cA
    @2
    vx
    @0
    vy
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
    @2
    @15
    vu
    cB
    nfcv
    vx
    @0
    cB
    nfcsb1v
    #
    vu
    cC
    nfcv
    vv
    cC
    nfcv
    vx
    @0
    @14
    nfcsb1v
    vy
    vx
    @0
    @14
    vy
    @0
    nfcv
    vy
    @13
    cC
    nfcsb1v
    nfcsb
    vx
    @0
    cB
    csbeq1a
    #
    vy
    cv
    @13
    wceq
    @5
    @0
    wceq
    #
    cC
    @14
    @15
    vy
    @13
    cC
    csbeq1a
    vx
    @0
    @14
    csbeq1a
    sylan9eqr
    cbvmpt2x
    fmpt2x.1
    vu
    vv
    vt
    cA
    @2
    @12
    @15
    @8
    @0
    @13
    cop
    wceq
    #
    @12
    vx
    @0
    @11
    csb
    @15
    @19
    vx
    @9
    @0
    @11
    @0
    @13
    @8
    vu
    vex
    #
    vv
    vex
    #
    op1std
    csbeq1d
    @19
    vx
    @0
    @11
    @14
    @19
    vy
    @10
    @13
    cC
    @0
    @13
    @8
    @20
    @21
    op2ndd
    csbeq1d
    csbeq2dv
    eqtrd
    mpt2mptx
    3eqtr4i
    dmmptss
    vx
    vu
    cA
    @7
    @3
    vu
    @7
    nfcv
    vx
    @1
    @2
    vx
    @1
    nfcv
    @16
    nfxp
    @18
    @6
    @1
    cB
    @2
    @5
    @0
    sneq
    @17
    xpeq12d
    cbviun
    sseqtr4i
end
