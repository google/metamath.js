include "cv.mm"
include "csp.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "chil.mm"
include "cno.mm"
include "wceq.mm"
include "oveq12.mm"
include "anidms.mm"
include "fveq2d.mm"
include "dfhnorm2.mm"
include "fvex.mm"
include "fvmpt.mm"

theorem normval
  let cA: class A
  let vx: setvar x


  assert |- ( A e. ~H -> ( normh ` A ) = ( sqrt ` ( A .ih A ) ) )

  proof
    vx
    cA
    vx
    cv
    #
    @0
    csp
    co
    #
    csqrt
    cfv
    cA
    cA
    csp
    co
    #
    csqrt
    cfv
    chil
    cno
    @0
    cA
    wceq
    #
    @1
    @2
    csqrt
    @3
    @1
    @2
    wceq
    @0
    cA
    @0
    cA
    csp
    oveq12
    anidms
    fveq2d
    vx
    dfhnorm2
    @2
    csqrt
    fvex
    fvmpt
end
