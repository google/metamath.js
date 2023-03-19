include "cvv.mm"
include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "vex.mm"
include "eldif.mm"
include "mpbiran.mm"
include "con2bii.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "ineqri.mm"

theorem dfin2
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A i^i B ) = ( A \ ( _V \ B ) )

  proof
    vx
    cA
    cB
    cA
    cvv
    cB
    cdif
    #
    cdif
    #
    vx
    cv
    #
    cA
    wcel
    #
    @2
    cB
    wcel
    #
    wa
    @3
    @2
    @0
    wcel
    #
    wn
    #
    wa
    @2
    @1
    wcel
    @4
    @6
    @3
    @5
    @4
    @5
    @2
    cvv
    wcel
    @4
    wn
    vx
    vex
    @2
    cvv
    cB
    eldif
    mpbiran
    con2bii
    anbi2i
    @2
    cA
    @0
    eldif
    bitr4i
    ineqri
end
