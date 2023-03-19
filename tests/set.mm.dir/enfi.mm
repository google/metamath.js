include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "com.mm"
include "wrex.mm"
include "cfn.mm"
include "wcel.mm"
include "enen1.mm"
include "rexbidv.mm"
include "isfi.mm"
include "3bitr4g.mm"

theorem enfi
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( A ~~ B -> ( A e. Fin <-> B e. Fin ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cA
    vx
    cv
    #
    cen
    wbr
    #
    vx
    com
    wrex
    cB
    @1
    cen
    wbr
    #
    vx
    com
    wrex
    cA
    cfn
    wcel
    cB
    cfn
    wcel
    @0
    @2
    @3
    vx
    com
    cA
    cB
    @1
    enen1
    rexbidv
    vx
    cA
    isfi
    vx
    cB
    isfi
    3bitr4g
end
