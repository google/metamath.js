include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wi.mm"
include "wa.mm"
include "wceq.mm"
include "wss.mm"
include "albiim.mm"
include "dfcleq.mm"
include "dfss2.mm"
include "anbi12i.mm"
include "3bitr4i.mm"

theorem eqss
  param cA: class A
  param cB: class B
  let vx: setvar x


  assert |- ( A = B <-> ( A C_ B /\ B C_ A ) )

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
    wb
    vx
    wal
    @1
    @2
    wi
    vx
    wal
    #
    @2
    @1
    wi
    vx
    wal
    #
    wa
    cA
    cB
    wceq
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wa
    @1
    @2
    vx
    albiim
    vx
    cA
    cB
    dfcleq
    @5
    @3
    @6
    @4
    vx
    cA
    cB
    dfss2
    vx
    cB
    cA
    dfss2
    anbi12i
    3bitr4i
end
