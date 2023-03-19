include "cin.mm"
include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "elin.mm"
include "eldif.mm"
include "orbi12i.mm"
include "pm4.42.mm"
include "bitr4i.mm"
include "uneqri.mm"

theorem inundif
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A i^i B ) u. ( A \ B ) ) = A

  proof
    vx
    cA
    cB
    cin
    #
    cA
    cB
    cdif
    #
    cA
    vx
    cv
    #
    @0
    wcel
    #
    @2
    @1
    wcel
    #
    wo
    @2
    cA
    wcel
    #
    @2
    cB
    wcel
    #
    wa
    #
    @5
    @6
    wn
    wa
    #
    wo
    @5
    @3
    @7
    @4
    @8
    @2
    cA
    cB
    elin
    @2
    cA
    cB
    eldif
    orbi12i
    @5
    @6
    pm4.42
    bitr4i
    uneqri
end
