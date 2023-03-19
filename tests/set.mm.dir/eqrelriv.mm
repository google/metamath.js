include "wrel.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "gen2.mm"
include "eqrel.mm"
include "mpbiri.mm"

theorem eqrelriv
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume eqrelriv.1: |- ( <. x , y >. e. A <-> <. x , y >. e. B )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( ( Rel A /\ Rel B ) -> A = B )

  proof
    cA
    wrel
    cB
    wrel
    wa
    cA
    cB
    wceq
    vx
    cv
    vy
    cv
    cop
    #
    cA
    wcel
    @0
    cB
    wcel
    wb
    #
    vy
    wal
    vx
    wal
    @1
    vx
    vy
    eqrelriv.1
    gen2
    vx
    vy
    cA
    cB
    eqrel
    mpbiri
end
