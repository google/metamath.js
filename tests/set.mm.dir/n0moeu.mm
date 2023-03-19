include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wmo.mm"
include "wex.mm"
include "wa.mm"
include "weu.mm"
include "n0.mm"
include "biimpi.mm"
include "biantrurd.mm"
include "eu5.mm"
include "syl6bbr.mm"

theorem n0moeu
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A =/= (/) -> ( E* x x e. A <-> E! x x e. A ) )

  proof
    cA
    c0
    wne
    #
    vx
    cv
    cA
    wcel
    #
    vx
    wmo
    #
    @1
    vx
    wex
    #
    @2
    wa
    @1
    vx
    weu
    @0
    @3
    @2
    @0
    @3
    vx
    cA
    n0
    biimpi
    biantrurd
    @1
    vx
    eu5
    syl6bbr
end
