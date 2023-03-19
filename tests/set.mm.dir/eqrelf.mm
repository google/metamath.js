include "wrel.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "eqrel.mm"
include "nfv.mm"
include "nfel2.mm"
include "nfbi.mm"
include "opeq12.mm"
include "eleq1d.mm"
include "bibi12d.mm"
include "cbval2.mm"
include "syl6bbr.mm"

theorem eqrelf
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vu: setvar u
  let vv: setvar v
  assume eqrelf.1: |- F/_ x A
  assume eqrelf.2: |- F/_ x B
  assume eqrelf.3: |- F/_ y A
  assume eqrelf.4: |- F/_ y B

  disjoint x y
  disjoint A u
  disjoint A v
  disjoint u v
  disjoint B u
  disjoint B v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  assert |- ( ( Rel A /\ Rel B ) -> ( A = B <-> A. x A. y ( <. x , y >. e. A <-> <. x , y >. e. B ) ) )

  proof
    cA
    wrel
    cB
    wrel
    wa
    cA
    cB
    wceq
    vu
    cv
    #
    vv
    cv
    #
    cop
    #
    cA
    wcel
    #
    @2
    cB
    wcel
    #
    wb
    #
    vv
    wal
    vu
    wal
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cA
    wcel
    #
    @8
    cB
    wcel
    #
    wb
    #
    vy
    wal
    vx
    wal
    vu
    vv
    cA
    cB
    eqrel
    @11
    @5
    vx
    vy
    vu
    vv
    @11
    vu
    nfv
    @11
    vv
    nfv
    @3
    @4
    vx
    vx
    @2
    cA
    eqrelf.1
    nfel2
    vx
    @2
    cB
    eqrelf.2
    nfel2
    nfbi
    @3
    @4
    vy
    vy
    @2
    cA
    eqrelf.3
    nfel2
    vy
    @2
    cB
    eqrelf.4
    nfel2
    nfbi
    @6
    @0
    wceq
    @7
    @1
    wceq
    wa
    #
    @9
    @3
    @10
    @4
    @12
    @8
    @2
    cA
    @6
    @7
    @0
    @1
    opeq12
    #
    eleq1d
    @12
    @8
    @2
    cB
    @13
    eleq1d
    bibi12d
    cbval2
    syl6bbr
end
