include "wfun.mm"
include "wdisj.mm"
include "ccnv.mm"
include "cima.mm"
include "cv.mm"
include "wceq.mm"
include "csb.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "wral.mm"
include "inpreima.mm"
include "imaeq2.mm"
include "ima0.mm"
include "syl6eq.mm"
include "sylan9req.mm"
include "ex.mm"
include "csbima12.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "csbconstg.mm"
include "ax-mp.mm"
include "imaeq1i.mm"
include "eqtri.mm"
include "ineq12i.mm"
include "eqeq1i.mm"
include "syl6ibr.mm"
include "orim2d.mm"
include "ralimdv.mm"
include "disjors.mm"
include "3imtr4g.mm"
include "imp.mm"

theorem disjpreima
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint F x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F y
  disjoint F z
  disjoint B y
  disjoint B z
  assert |- ( ( Fun F /\ Disj_ x e. A B ) -> Disj_ x e. A ( `' F " B ) )

  proof
    cF
    wfun
    #
    vx
    cA
    cB
    wdisj
    #
    vx
    cA
    cF
    ccnv
    #
    cB
    cima
    #
    wdisj
    #
    @0
    vy
    cv
    #
    vz
    cv
    #
    wceq
    #
    vx
    @5
    cB
    csb
    #
    vx
    @6
    cB
    csb
    #
    cin
    #
    c0
    wceq
    #
    wo
    #
    vz
    cA
    wral
    #
    vy
    cA
    wral
    @7
    vx
    @5
    @3
    csb
    #
    vx
    @6
    @3
    csb
    #
    cin
    #
    c0
    wceq
    #
    wo
    #
    vz
    cA
    wral
    #
    vy
    cA
    wral
    @1
    @4
    @0
    @13
    @19
    vy
    cA
    @0
    @12
    @18
    vz
    cA
    @0
    @11
    @17
    @7
    @0
    @11
    @2
    @8
    cima
    #
    @2
    @9
    cima
    #
    cin
    #
    c0
    wceq
    #
    @17
    @0
    @11
    @23
    @0
    @11
    @22
    @2
    @10
    cima
    #
    c0
    @8
    @9
    cF
    inpreima
    @11
    @24
    @2
    c0
    cima
    c0
    @10
    c0
    @2
    imaeq2
    @2
    ima0
    syl6eq
    sylan9req
    ex
    @16
    @22
    c0
    @14
    @20
    @15
    @21
    @14
    vx
    @5
    @2
    csb
    #
    @8
    cima
    @20
    vx
    @5
    cB
    @2
    csbima12
    @25
    @2
    @8
    @5
    cvv
    wcel
    @25
    @2
    wceq
    vy
    vex
    vx
    @5
    @2
    cvv
    csbconstg
    ax-mp
    imaeq1i
    eqtri
    @15
    vx
    @6
    @2
    csb
    #
    @9
    cima
    @21
    vx
    @6
    cB
    @2
    csbima12
    @26
    @2
    @9
    @6
    cvv
    wcel
    @26
    @2
    wceq
    vz
    vex
    vx
    @6
    @2
    cvv
    csbconstg
    ax-mp
    imaeq1i
    eqtri
    ineq12i
    eqeq1i
    syl6ibr
    orim2d
    ralimdv
    ralimdv
    vx
    cA
    cB
    vy
    vz
    disjors
    vx
    cA
    @3
    vy
    vz
    disjors
    3imtr4g
    imp
end
