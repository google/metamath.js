include "cvv.mm"
include "c0.mm"
include "wne.mm"
include "cdif.mm"
include "vn0.mm"
include "wceq.mm"
include "id.mm"
include "difeq1.mm"
include "difabs.mm"
include "difid.mm"
include "3eqtr3g.mm"
include "eqtr3d.mm"
include "difeq2d.mm"
include "dif0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "ax-mp.mm"

theorem compne
  let cA: class A


  assert |- ( _V \ A ) =/= A

  proof
    cvv
    c0
    wne
    cvv
    cA
    cdif
    #
    cA
    wne
    vn0
    @0
    cA
    cvv
    c0
    @0
    cA
    wceq
    #
    @0
    cvv
    c0
    @1
    @0
    cvv
    c0
    cdif
    cvv
    @1
    cA
    c0
    cvv
    @1
    @0
    cA
    c0
    @1
    id
    @1
    @0
    cA
    cdif
    cA
    cA
    cdif
    @0
    c0
    @0
    cA
    cA
    difeq1
    cvv
    cA
    difabs
    cA
    difid
    3eqtr3g
    #
    eqtr3d
    difeq2d
    cvv
    dif0
    syl6eq
    @2
    eqtr3d
    necon3i
    ax-mp
end
