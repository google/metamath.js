include "crnk.mm"
include "cfv.mm"
include "cuni.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wceq.mm"
include "rankuniss.mm"
include "biantru.mm"
include "csuc.mm"
include "ciun.mm"
include "iunss.mm"
include "rankval4.mm"
include "sseq1i.mm"
include "rankon.mm"
include "onsucssi.mm"
include "ralbii.mm"
include "3bitr4ri.mm"
include "eqss.mm"
include "3bitr4i.mm"

theorem rankc1
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let cB: class B
  assume rankr1b.1: |- A e. _V

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B x
  assert |- ( A. x e. A ( rank ` x ) e. ( rank ` U. A ) <-> ( rank ` A ) = ( rank ` U. A ) )

  proof
    cA
    crnk
    cfv
    #
    cA
    cuni
    #
    crnk
    cfv
    #
    wss
    #
    @3
    @2
    @0
    wss
    #
    wa
    vx
    cv
    #
    crnk
    cfv
    #
    @2
    wcel
    #
    vx
    cA
    wral
    #
    @0
    @2
    wceq
    @4
    @3
    cA
    rankr1b.1
    rankuniss
    biantru
    vx
    cA
    @6
    csuc
    #
    ciun
    #
    @2
    wss
    @9
    @2
    wss
    #
    vx
    cA
    wral
    @3
    @8
    vx
    cA
    @9
    @2
    iunss
    @0
    @10
    @2
    vx
    cA
    rankr1b.1
    rankval4
    sseq1i
    @7
    @11
    vx
    cA
    @6
    @2
    @5
    rankon
    @1
    rankon
    onsucssi
    ralbii
    3bitr4ri
    @0
    @2
    eqss
    3bitr4i
end
