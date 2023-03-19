include "cfn.mm"
include "wss.mm"
include "wcel.mm"
include "cv.mm"
include "wral.mm"
include "cuni.mm"
include "dfss3.mm"
include "wa.mm"
include "ciun.mm"
include "uniiun.mm"
include "iunfi.mm"
include "syl5eqel.mm"
include "sylan2b.mm"

theorem unifi
  let cA: class A
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B


  assert |- ( ( A e. Fin /\ A C_ Fin ) -> U. A e. Fin )

  proof
    cA
    cfn
    wss
    cA
    cfn
    wcel
    #
    vx
    cv
    #
    cfn
    wcel
    vx
    cA
    wral
    #
    cA
    cuni
    #
    cfn
    wcel
    vx
    cA
    cfn
    dfss3
    @0
    @2
    wa
    @3
    vx
    cA
    @1
    ciun
    cfn
    vx
    cA
    uniiun
    vx
    cA
    @1
    iunfi
    syl5eqel
    sylan2b
end
