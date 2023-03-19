include "c0.mm"
include "cv.mm"
include "wcel.mm"
include "wo.mm"
include "noel.mm"
include "biorfi.mm"
include "bicomi.mm"
include "uneqri.mm"

theorem un0
  let cA: class A
  let vx: setvar x


  assert |- ( A u. (/) ) = A

  proof
    vx
    cA
    c0
    cA
    vx
    cv
    #
    cA
    wcel
    #
    @1
    @0
    c0
    wcel
    #
    wo
    @2
    @1
    @0
    noel
    biorfi
    bicomi
    uneqri
end
