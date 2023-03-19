include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wceq.mm"
include "wex.mm"
include "cab.mm"
include "cres.mm"
include "cvv.mm"
include "wss.mm"
include "ssv.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "fveq1i.mm"
include "wcel.mm"
include "vex.mm"
include "fveq2.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "fveqres.mm"
include "eqtr3i.mm"
include "eqeq2i.mm"
include "exbii.mm"
include "abbii.mm"
include "mptex.mm"
include "fvclex.mm"
include "eqeltrri.mm"

theorem fvresex
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let vz: setvar z
  assume fvresex.1: |- A e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint F z
  assert |- { y | E. x y = ( ( F |` A ) ` x ) } e. _V

  proof
    vy
    cv
    #
    vx
    cv
    #
    vz
    cA
    vz
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    cfv
    #
    wceq
    #
    vx
    wex
    #
    vy
    cab
    @0
    @1
    cF
    cA
    cres
    cfv
    #
    wceq
    #
    vx
    wex
    #
    vy
    cab
    cvv
    @7
    @10
    vy
    @6
    @9
    vx
    @5
    @8
    @0
    @1
    vz
    cvv
    @3
    cmpt
    #
    cA
    cres
    #
    cfv
    #
    @5
    @8
    @1
    @12
    @4
    cA
    cvv
    wss
    @12
    @4
    wceq
    cA
    ssv
    vz
    cvv
    cA
    @3
    resmpt
    ax-mp
    fveq1i
    @1
    @11
    cfv
    @1
    cF
    cfv
    #
    wceq
    #
    @13
    @8
    wceq
    @1
    cvv
    wcel
    @15
    vx
    vex
    vz
    @1
    @3
    @14
    cvv
    @11
    @2
    @1
    cF
    fveq2
    @11
    eqid
    @1
    cF
    fvex
    fvmpt
    ax-mp
    @1
    cA
    @11
    cF
    fveqres
    ax-mp
    eqtr3i
    eqeq2i
    exbii
    abbii
    vx
    vy
    @4
    vz
    cA
    @3
    fvresex.1
    mptex
    fvclex
    eqeltrri
end
