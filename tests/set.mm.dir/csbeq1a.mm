include "cv.mm"
include "wceq.mm"
include "csb.mm"
include "csbid.mm"
include "csbeq1.mm"
include "syl5eqr.mm"

theorem csbeq1a
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- ( x = A -> B = [_ A / x ]_ B )

  proof
    vx
    cv
    #
    cA
    wceq
    cB
    vx
    @0
    cB
    csb
    vx
    cA
    cB
    csb
    vx
    cB
    csbid
    vx
    @0
    cA
    cB
    csbeq1
    syl5eqr
end
