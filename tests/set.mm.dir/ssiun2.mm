include "cv.mm"
include "wcel.mm"
include "ciun.mm"
include "wrex.mm"
include "rspe.mm"
include "ex.mm"
include "eliun.mm"
include "syl6ibr.mm"
include "ssrdv.mm"

theorem ssiun2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y


  assert |- ( x e. A -> B C_ U_ x e. A B )

  proof
    vx
    cv
    cA
    wcel
    #
    vy
    cB
    vx
    cA
    cB
    ciun
    #
    @0
    vy
    cv
    #
    cB
    wcel
    #
    @3
    vx
    cA
    wrex
    #
    @2
    @1
    wcel
    @0
    @3
    @4
    @3
    vx
    cA
    rspe
    ex
    vx
    @2
    cA
    cB
    eliun
    syl6ibr
    ssrdv
end
