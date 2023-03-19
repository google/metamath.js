include "c0.mm"
include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "wn.mm"
include "noel.mm"
include "a1i.mm"
include "nrex.mm"
include "eliun.mm"
include "mtbir.mm"
include "nel0.mm"

theorem iun0
  let vx: setvar x
  let cA: class A
  let vy: setvar y


  assert |- U_ x e. A (/) = (/)

  proof
    vy
    vx
    cA
    c0
    ciun
    #
    vy
    cv
    #
    @0
    wcel
    @1
    c0
    wcel
    #
    vx
    cA
    wrex
    @2
    vx
    cA
    @2
    wn
    vx
    cv
    cA
    wcel
    @1
    noel
    a1i
    nrex
    vx
    @1
    cA
    c0
    eliun
    mtbir
    nel0
end
