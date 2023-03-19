include "cvv.mm"
include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "vex.mm"
include "eldif.mm"
include "mpbiran.mm"
include "con2bii.mm"
include "biantrur.mm"
include "bitr2i.mm"
include "difeqri.mm"

theorem ddif
  let cA: class A
  let vx: setvar x


  assert |- ( _V \ ( _V \ A ) ) = A

  proof
    vx
    cvv
    cvv
    cA
    cdif
    #
    cA
    vx
    cv
    #
    cA
    wcel
    #
    @1
    @0
    wcel
    #
    wn
    #
    @1
    cvv
    wcel
    #
    @4
    wa
    @3
    @2
    @3
    @5
    @2
    wn
    vx
    vex
    #
    @1
    cvv
    cA
    eldif
    mpbiran
    con2bii
    @5
    @4
    @6
    biantrur
    bitr2i
    difeqri
end
