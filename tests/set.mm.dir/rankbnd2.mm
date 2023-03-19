include "cv.mm"
include "crnk.mm"
include "cfv.mm"
include "wss.mm"
include "wral.mm"
include "cuni.mm"
include "con0.mm"
include "wcel.mm"
include "csuc.mm"
include "ciun.mm"
include "rankuni.mm"
include "rankuni2.mm"
include "eqtr3i.mm"
include "sseq1i.mm"
include "iunss.mm"
include "bitr2i.mm"
include "word.mm"
include "wb.mm"
include "rankon.mm"
include "onssi.mm"
include "eloni.mm"
include "ordunisssuc.mm"
include "sylancr.mm"
include "syl5bb.mm"

theorem rankbnd2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume rankr1b.1: |- A e. _V

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  assert |- ( B e. On -> ( A. x e. A ( rank ` x ) C_ B <-> ( rank ` A ) C_ suc B ) )

  proof
    vx
    cv
    crnk
    cfv
    #
    cB
    wss
    vx
    cA
    wral
    #
    cA
    crnk
    cfv
    #
    cuni
    #
    cB
    wss
    #
    cB
    con0
    wcel
    #
    @2
    cB
    csuc
    wss
    #
    @4
    vx
    cA
    @0
    ciun
    #
    cB
    wss
    @1
    @3
    @7
    cB
    cA
    cuni
    crnk
    cfv
    @3
    @7
    cA
    rankuni
    vx
    cA
    rankr1b.1
    rankuni2
    eqtr3i
    sseq1i
    vx
    cA
    @0
    cB
    iunss
    bitr2i
    @5
    @2
    con0
    wss
    cB
    word
    @4
    @6
    wb
    @2
    cA
    rankon
    onssi
    cB
    eloni
    @2
    cB
    ordunisssuc
    sylancr
    syl5bb
end
