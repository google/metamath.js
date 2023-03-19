include "cuni.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "wex.mm"
include "eluni.mm"
include "nfcv.mm"
include "nfel.mm"
include "nfan.mm"
include "nfv.mm"
include "weq.mm"
include "eleq2.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "cbvex.mm"
include "bitri.mm"

theorem elunif
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume elunif.1: |- F/_ x A
  assume elunif.2: |- F/_ x B

  disjoint A B
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A e. U. B <-> E. x ( A e. x /\ x e. B ) )

  proof
    cA
    cB
    cuni
    wcel
    cA
    vy
    cv
    #
    wcel
    #
    @0
    cB
    wcel
    #
    wa
    #
    vy
    wex
    cA
    vx
    cv
    #
    wcel
    #
    @4
    cB
    wcel
    #
    wa
    #
    vx
    wex
    vy
    cA
    cB
    eluni
    @3
    @7
    vy
    vx
    @1
    @2
    vx
    vx
    cA
    @0
    elunif.1
    vx
    @0
    nfcv
    #
    nfel
    vx
    @0
    cB
    @8
    elunif.2
    nfel
    nfan
    @7
    vy
    nfv
    vy
    vx
    weq
    @1
    @5
    @2
    @6
    @0
    @4
    cA
    eleq2
    @0
    @4
    cB
    eleq1
    anbi12d
    cbvex
    bitri
end
