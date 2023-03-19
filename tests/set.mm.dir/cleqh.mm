include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "dfcleq.mm"
include "nfv.mm"
include "nf5i.mm"
include "nfbi.mm"
include "weq.mm"
include "eleq1.mm"
include "bibi12d.mm"
include "cbvalv1.mm"
include "bitr4i.mm"

theorem cleqh
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume cleqh.1: |- ( y e. A -> A. x y e. A )
  assume cleqh.2: |- ( y e. B -> A. x y e. B )

  disjoint A y
  disjoint B y
  disjoint x y
  assert |- ( A = B <-> A. x ( x e. A <-> x e. B ) )

  proof
    cA
    cB
    wceq
    vy
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
    #
    vy
    wal
    vx
    cv
    #
    cA
    wcel
    #
    @4
    cB
    wcel
    #
    wb
    #
    vx
    wal
    vy
    cA
    cB
    dfcleq
    @7
    @3
    vx
    vy
    @7
    vy
    nfv
    @1
    @2
    vx
    @1
    vx
    cleqh.1
    nf5i
    @2
    vx
    cleqh.2
    nf5i
    nfbi
    vx
    vy
    weq
    @5
    @1
    @6
    @2
    @4
    @0
    cA
    eleq1
    @4
    @0
    cB
    eleq1
    bibi12d
    cbvalv1
    bitr4i
end
