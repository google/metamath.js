include "c0.mm"
include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "rex0.mm"
include "eliun.mm"
include "mtbir.mm"
include "nel0.mm"

theorem 0iun
  let vx: setvar x
  let cA: class A
  let vy: setvar y


  assert |- U_ x e. (/) A = (/)

  proof
    vy
    vx
    c0
    cA
    ciun
    #
    vy
    cv
    #
    @0
    wcel
    @1
    cA
    wcel
    #
    vx
    c0
    wrex
    @2
    vx
    rex0
    vx
    @1
    c0
    cA
    eliun
    mtbir
    nel0
end
