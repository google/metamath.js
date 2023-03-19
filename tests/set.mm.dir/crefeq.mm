include "wceq.mm"
include "cv.mm"
include "cuni.mm"
include "cref.mm"
include "wbr.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "ctop.mm"
include "crab.mm"
include "ccref.mm"
include "ineq2.mm"
include "rexeqdv.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "rabbidv.mm"
include "df-cref.mm"
include "3eqtr4g.mm"

theorem crefeq
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vy: setvar y
  let vz: setvar z


  assert |- ( A = B -> CovHasRef A = CovHasRef B )

  proof
    cA
    cB
    wceq
    #
    vj
    cv
    #
    cuni
    vy
    cv
    #
    cuni
    wceq
    #
    vz
    cv
    @2
    cref
    wbr
    #
    vz
    @1
    cpw
    #
    cA
    cin
    #
    wrex
    #
    wi
    #
    vy
    @5
    wral
    #
    vj
    ctop
    crab
    @3
    @4
    vz
    @5
    cB
    cin
    #
    wrex
    #
    wi
    #
    vy
    @5
    wral
    #
    vj
    ctop
    crab
    cA
    ccref
    cB
    ccref
    @0
    @9
    @13
    vj
    ctop
    @0
    @8
    @12
    vy
    @5
    @0
    @7
    @11
    @3
    @0
    @4
    vz
    @6
    @10
    cA
    cB
    @5
    ineq2
    rexeqdv
    imbi2d
    ralbidv
    rabbidv
    vy
    vz
    cA
    vj
    df-cref
    vy
    vz
    cB
    vj
    df-cref
    3eqtr4g
end
