include "cv.mm"
include "crnk.mm"
include "cfv.mm"
include "cuni.mm"
include "wceq.mm"
include "wrex.mm"
include "csuc.mm"
include "wss.mm"
include "cpw.mm"
include "pwuni.mm"
include "uniex.mm"
include "pwex.mm"
include "rankss.mm"
include "ax-mp.mm"
include "rankpw.mm"
include "sseqtri.mm"
include "a1i.mm"
include "wcel.mm"
include "rankel.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "rankon.mm"
include "onsucssi.mm"
include "sylib.mm"
include "eqssd.mm"

theorem rankc2
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let cB: class B
  assume rankr1b.1: |- A e. _V

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B x
  assert |- ( E. x e. A ( rank ` x ) = ( rank ` U. A ) -> ( rank ` A ) = suc ( rank ` U. A ) )

  proof
    vx
    cv
    #
    crnk
    cfv
    #
    cA
    cuni
    #
    crnk
    cfv
    #
    wceq
    #
    vx
    cA
    wrex
    #
    cA
    crnk
    cfv
    #
    @3
    csuc
    #
    @6
    @7
    wss
    @5
    @6
    @2
    cpw
    #
    crnk
    cfv
    #
    @7
    cA
    @8
    wss
    @6
    @9
    wss
    cA
    pwuni
    cA
    @8
    @2
    cA
    rankr1b.1
    uniex
    #
    pwex
    rankss
    ax-mp
    @2
    @10
    rankpw
    sseqtri
    a1i
    @5
    @3
    @6
    wcel
    #
    @7
    @6
    wss
    @4
    @11
    vx
    cA
    @0
    cA
    wcel
    @1
    @6
    wcel
    @4
    @11
    @0
    cA
    rankr1b.1
    rankel
    @1
    @3
    @6
    eleq1
    syl5ibcom
    rexlimiv
    @3
    @6
    @2
    rankon
    cA
    rankon
    onsucssi
    sylib
    eqssd
end
