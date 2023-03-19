include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "cun.mm"
include "wb.mm"
include "wss.mm"
include "wceq.mm"
include "wo.mm"
include "bicom.mm"
include "pm4.72.mm"
include "elun.mm"
include "bibi1i.mm"
include "3bitr4i.mm"
include "albii.mm"
include "dfss2.mm"
include "dfcleq.mm"

theorem ssequn1
  let cA: class A
  let cB: class B
  let vx: setvar x
  let cC: class C


  assert |- ( A C_ B <-> ( A u. B ) = B )

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
    #
    wi
    #
    vx
    wal
    @0
    cA
    cB
    cun
    #
    wcel
    #
    @2
    wb
    #
    vx
    wal
    cA
    cB
    wss
    @4
    cB
    wceq
    @3
    @6
    vx
    @2
    @1
    @2
    wo
    #
    wb
    @7
    @2
    wb
    @3
    @6
    @2
    @7
    bicom
    @1
    @2
    pm4.72
    @5
    @7
    @2
    @0
    cA
    cB
    elun
    bibi1i
    3bitr4i
    albii
    vx
    cA
    cB
    dfss2
    vx
    @4
    cB
    dfcleq
    3bitr4i
end
