include "cv.mm"
include "csn.mm"
include "csb.mm"
include "cxp.mm"
include "ciun.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "cop.mm"
include "wceq.mm"
include "vex.mm"
include "op1std.mm"
include "csbeq1d.mm"
include "op2ndd.mm"
include "csbeq2dv.mm"
include "eqtrd.mm"
include "mpt2mptx.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfxp.mm"
include "sneq.mm"
include "csbeq1a.mm"
include "xpeq12d.mm"
include "cbviun.mm"
include "mpteq1.mm"
include "ax-mp.mm"
include "nfcsb.mm"
include "sylan9eqr.mm"
include "cbvmpt2x.mm"
include "3eqtr4ri.mm"

theorem mpt2mptsx
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vu: setvar u
  let vv: setvar v

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint B u
  disjoint B v
  disjoint C u
  disjoint C v
  assert |- ( x e. A , y e. B |-> C ) = ( z e. U_ x e. A ( { x } X. B ) |-> [_ ( 1st ` z ) / x ]_ [_ ( 2nd ` z ) / y ]_ C )

  proof
    vz
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
    vz
    cv
    #
    c1st
    cfv
    #
    vy
    @5
    c2nd
    cfv
    #
    cC
    csb
    #
    csb
    #
    cmpt
    #
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
    vz
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
    #
    @9
    cmpt
    #
    vx
    vy
    cA
    cB
    cC
    cmpt2
    vu
    vv
    vz
    cA
    @2
    @9
    @13
    @5
    @0
    @11
    cop
    wceq
    #
    @9
    vx
    @0
    @8
    csb
    @13
    @19
    vx
    @6
    @0
    @8
    @0
    @11
    @5
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
    @8
    @12
    @19
    vy
    @7
    @11
    cC
    @0
    @11
    @5
    @20
    @21
    op2ndd
    csbeq1d
    csbeq2dv
    eqtrd
    mpt2mptx
    @17
    @4
    wceq
    @18
    @10
    wceq
    vx
    vu
    cA
    @16
    @3
    vu
    @16
    nfcv
    vx
    @1
    @2
    vx
    @1
    nfcv
    vx
    @0
    cB
    nfcsb1v
    #
    nfxp
    @14
    @0
    wceq
    #
    @15
    @1
    cB
    @2
    @14
    @0
    sneq
    vx
    @0
    cB
    csbeq1a
    #
    xpeq12d
    cbviun
    vz
    @17
    @4
    @9
    mpteq1
    ax-mp
    vx
    vy
    vu
    vv
    cA
    cB
    cC
    @2
    @13
    vu
    cB
    nfcv
    @22
    vu
    cC
    nfcv
    vv
    cC
    nfcv
    vx
    @0
    @12
    nfcsb1v
    vy
    vx
    @0
    @12
    vy
    @0
    nfcv
    vy
    @11
    cC
    nfcsb1v
    nfcsb
    @24
    vy
    cv
    @11
    wceq
    @23
    cC
    @12
    @13
    vy
    @11
    cC
    csbeq1a
    vx
    @0
    @12
    csbeq1a
    sylan9eqr
    cbvmpt2x
    3eqtr4ri
end
