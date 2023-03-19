include "cin.mm"
include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wn.mm"
include "wa.mm"
include "pm4.61.mm"
include "anclb.mm"
include "elin.mm"
include "imbi2i.mm"
include "iman.mm"
include "3bitr2i.mm"
include "con2bii.mm"
include "eldif.mm"
include "3bitr4i.mm"
include "difeqri.mm"

theorem difin
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A \ ( A i^i B ) ) = ( A \ B )

  proof
    vx
    cA
    cA
    cB
    cin
    #
    cA
    cB
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
    wi
    #
    wn
    @3
    @4
    wn
    wa
    @3
    @2
    @0
    wcel
    #
    wn
    wa
    #
    @2
    @1
    wcel
    @3
    @4
    pm4.61
    @5
    @7
    @5
    @3
    @3
    @4
    wa
    #
    wi
    @3
    @6
    wi
    @7
    wn
    @3
    @4
    anclb
    @6
    @8
    @3
    @2
    cA
    cB
    elin
    imbi2i
    @3
    @6
    iman
    3bitr2i
    con2bii
    @2
    cA
    cB
    eldif
    3bitr4i
    difeqri
end
