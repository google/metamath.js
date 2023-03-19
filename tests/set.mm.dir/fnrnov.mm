include "cxp.mm"
include "wfn.mm"
include "crn.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "co.mm"
include "fnrnfv.mm"
include "cop.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "eqeq2d.mm"
include "rexxp.mm"
include "abbii.mm"
include "syl6eq.mm"

theorem fnrnov
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cF: class F
  let vw: setvar w
  let cC: class C

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint C w
  disjoint C z
  disjoint F w
  assert |- ( F Fn ( A X. B ) -> ran F = { z | E. x e. A E. y e. B z = ( x F y ) } )

  proof
    cF
    cA
    cB
    cxp
    #
    wfn
    cF
    crn
    vz
    cv
    #
    vw
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vw
    @0
    wrex
    #
    vz
    cab
    @1
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
    vw
    vz
    @0
    cF
    fnrnfv
    @5
    @10
    vz
    @4
    @9
    vw
    vx
    vy
    cA
    cB
    @2
    @6
    @7
    cop
    #
    wceq
    #
    @3
    @8
    @1
    @12
    @3
    @11
    cF
    cfv
    @8
    @2
    @11
    cF
    fveq2
    @6
    @7
    cF
    df-ov
    syl6eqr
    eqeq2d
    rexxp
    abbii
    syl6eq
end
