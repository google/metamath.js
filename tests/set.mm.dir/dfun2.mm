include "cvv.mm"
include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "vex.mm"
include "eldif.mm"
include "mpbiran.mm"
include "anbi1i.mm"
include "ioran.mm"
include "3bitr4i.mm"
include "con2bii.mm"
include "bitr4i.mm"
include "uneqri.mm"

theorem dfun2
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A u. B ) = ( _V \ ( ( _V \ A ) \ B ) )

  proof
    vx
    cA
    cB
    cvv
    cvv
    cA
    cdif
    #
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
    @3
    cB
    wcel
    #
    wo
    #
    @3
    @1
    wcel
    #
    wn
    #
    @3
    @2
    wcel
    #
    @7
    @6
    @3
    @0
    wcel
    #
    @5
    wn
    #
    wa
    @4
    wn
    #
    @11
    wa
    @7
    @6
    wn
    @10
    @12
    @11
    @10
    @3
    cvv
    wcel
    #
    @12
    vx
    vex
    #
    @3
    cvv
    cA
    eldif
    mpbiran
    anbi1i
    @3
    @0
    cB
    eldif
    @4
    @5
    ioran
    3bitr4i
    con2bii
    @9
    @13
    @8
    @14
    @3
    cvv
    @1
    eldif
    mpbiran
    bitr4i
    uneqri
end
