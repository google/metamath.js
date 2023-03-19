include "wrel.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wceq.mm"
include "wb.mm"
include "ssrel.mm"
include "bi2anan9.mm"
include "eqss.mm"
include "2albiim.mm"
include "3bitr4g.mm"

theorem eqrel
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  assert |- ( ( Rel A /\ Rel B ) -> ( A = B <-> A. x A. y ( <. x , y >. e. A <-> <. x , y >. e. B ) ) )

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
    vy
    cv
    cop
    #
    cA
    wcel
    #
    @4
    cB
    wcel
    #
    wi
    vy
    wal
    vx
    wal
    #
    @6
    @5
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
    @5
    @6
    wb
    vy
    wal
    vx
    wal
    @0
    @2
    @7
    @1
    @3
    @8
    vx
    vy
    cA
    cB
    ssrel
    vx
    vy
    cB
    cA
    ssrel
    bi2anan9
    cA
    cB
    eqss
    @5
    @6
    vx
    vy
    2albiim
    3bitr4g
end
