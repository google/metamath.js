include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wa.mm"
include "wn.mm"
include "pm4.45im.mm"
include "iman.mm"
include "eldif.mm"
include "xchbinxr.mm"
include "anbi2i.mm"
include "bitr2i.mm"
include "difeqri.mm"

theorem difdif
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A \ ( B \ A ) ) = A

  proof
    vx
    cA
    cB
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
    @2
    @1
    cB
    wcel
    #
    @2
    wi
    #
    wa
    @2
    @1
    @0
    wcel
    #
    wn
    #
    wa
    @2
    @3
    pm4.45im
    @4
    @6
    @2
    @4
    @3
    @2
    wn
    wa
    @5
    @3
    @2
    iman
    @1
    cB
    cA
    eldif
    xchbinxr
    anbi2i
    bitr2i
    difeqri
end
