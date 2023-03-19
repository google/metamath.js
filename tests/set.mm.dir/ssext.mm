include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "wceq.mm"
include "wb.mm"
include "ssextss.mm"
include "anbi12i.mm"
include "eqss.mm"
include "albiim.mm"
include "3bitr4i.mm"

theorem ssext
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A = B <-> A. x ( x C_ A <-> x C_ B ) )

  proof
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wa
    vx
    cv
    #
    cA
    wss
    #
    @2
    cB
    wss
    #
    wi
    vx
    wal
    #
    @4
    @3
    wi
    vx
    wal
    #
    wa
    cA
    cB
    wceq
    @3
    @4
    wb
    vx
    wal
    @0
    @5
    @1
    @6
    vx
    cA
    cB
    ssextss
    vx
    cB
    cA
    ssextss
    anbi12i
    cA
    cB
    eqss
    @3
    @4
    vx
    albiim
    3bitr4i
end
