include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "cdif.mm"
include "wb.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "pm4.71.mm"
include "eldif.mm"
include "bibi2i.mm"
include "bitr4i.mm"
include "albii.mm"
include "disj1.mm"
include "dfcleq.mm"
include "3bitr4i.mm"

theorem disj3
  let cA: class A
  let cB: class B
  let vx: setvar x
  let cC: class C


  assert |- ( ( A i^i B ) = (/) <-> A = ( A \ B ) )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    @0
    cB
    wcel
    wn
    #
    wi
    #
    vx
    wal
    @1
    @0
    cA
    cB
    cdif
    #
    wcel
    #
    wb
    #
    vx
    wal
    cA
    cB
    cin
    c0
    wceq
    cA
    @4
    wceq
    @3
    @6
    vx
    @3
    @1
    @1
    @2
    wa
    #
    wb
    @6
    @1
    @2
    pm4.71
    @5
    @7
    @1
    @0
    cA
    cB
    eldif
    bibi2i
    bitr4i
    albii
    vx
    cA
    cB
    disj1
    vx
    cA
    @4
    dfcleq
    3bitr4i
end
