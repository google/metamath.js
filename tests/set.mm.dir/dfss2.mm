include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "wal.mm"
include "wi.mm"
include "cin.mm"
include "wceq.mm"
include "cab.mm"
include "dfss.mm"
include "df-in.mm"
include "eqeq2i.mm"
include "abeq2.mm"
include "3bitri.mm"
include "pm4.71.mm"
include "albii.mm"
include "bitr4i.mm"

theorem dfss2
  param vx: setvar x
  param cA: class A
  param cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A C_ B <-> A. x ( x e. A -> x e. B ) )

  proof
    cA
    cB
    wss
    #
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
    wa
    #
    wb
    #
    vx
    wal
    #
    @2
    @3
    wi
    #
    vx
    wal
    @0
    cA
    cA
    cB
    cin
    #
    wceq
    cA
    @4
    vx
    cab
    #
    wceq
    @6
    cA
    cB
    dfss
    @8
    @9
    cA
    vx
    cA
    cB
    df-in
    eqeq2i
    @4
    vx
    cA
    abeq2
    3bitri
    @7
    @5
    vx
    @2
    @3
    pm4.71
    albii
    bitr4i
end
