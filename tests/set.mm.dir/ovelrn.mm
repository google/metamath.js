include "cxp.mm"
include "wfn.mm"
include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "fnrnov.mm"
include "eleq2d.mm"
include "cvv.mm"
include "ovex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "rexlimivw.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "elab3.mm"
include "syl6bb.mm"

theorem ovelrn
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vz: setvar z
  let cD: class D

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint F x
  disjoint F y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint F z
  assert |- ( F Fn ( A X. B ) -> ( C e. ran F <-> E. x e. A E. y e. B C = ( x F y ) ) )

  proof
    cF
    cA
    cB
    cxp
    wfn
    #
    cC
    cF
    crn
    #
    wcel
    cC
    vz
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    wceq
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    #
    vz
    cab
    #
    wcel
    cC
    @5
    wceq
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    #
    @0
    @1
    @8
    cC
    vx
    vy
    vz
    cA
    cB
    cF
    fnrnov
    eleq2d
    @7
    @11
    vz
    cC
    @10
    cC
    cvv
    wcel
    #
    vx
    cA
    @9
    @12
    vy
    cB
    @9
    @12
    @5
    cvv
    wcel
    @3
    @4
    cF
    ovex
    cC
    @5
    cvv
    eleq1
    mpbiri
    rexlimivw
    rexlimivw
    @2
    cC
    wceq
    @6
    @9
    vx
    vy
    cA
    cB
    @2
    cC
    @5
    eqeq1
    2rexbidv
    elab3
    syl6bb
end
