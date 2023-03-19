include "c0.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "noel.mm"
include "bianfi.mm"
include "bicomi.mm"
include "ineqri.mm"

theorem in0
  let cA: class A
  let vx: setvar x


  assert |- ( A i^i (/) ) = (/)

  proof
    vx
    cA
    c0
    c0
    vx
    cv
    #
    c0
    wcel
    #
    @0
    cA
    wcel
    #
    @1
    wa
    @1
    @2
    @0
    noel
    bianfi
    bicomi
    ineqri
end
