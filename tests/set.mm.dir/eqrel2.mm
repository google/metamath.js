include "wrel.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "wceq.mm"
include "wb.mm"
include "ssrel3.mm"
include "bi2anan9.mm"
include "eqss.mm"
include "2albiim.mm"
include "3bitr4g.mm"

theorem eqrel2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  assert |- ( ( Rel A /\ Rel B ) -> ( A = B <-> A. x A. y ( x A y <-> x B y ) ) )

  proof
    cA
    wrel
    #
    cB
    wrel
    #
    wa
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
    vy
    cv
    #
    cA
    wbr
    #
    @4
    @5
    cB
    wbr
    #
    wi
    vy
    wal
    vx
    wal
    #
    @7
    @6
    wi
    vy
    wal
    vx
    wal
    #
    wa
    cA
    cB
    wceq
    @6
    @7
    wb
    vy
    wal
    vx
    wal
    @0
    @2
    @8
    @1
    @3
    @9
    vx
    vy
    cA
    cB
    ssrel3
    vx
    vy
    cB
    cA
    ssrel3
    bi2anan9
    cA
    cB
    eqss
    @6
    @7
    vx
    vy
    2albiim
    3bitr4g
end
