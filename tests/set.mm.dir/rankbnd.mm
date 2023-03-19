include "crnk.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "csuc.mm"
include "ciun.mm"
include "wral.mm"
include "rankval4.mm"
include "sseq1i.mm"
include "iunss.mm"
include "bitr2i.mm"

theorem rankbnd
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume rankr1b.1: |- A e. _V

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  assert |- ( A. x e. A suc ( rank ` x ) C_ B <-> ( rank ` A ) C_ B )

  proof
    cA
    crnk
    cfv
    #
    cB
    wss
    vx
    cA
    vx
    cv
    crnk
    cfv
    csuc
    #
    ciun
    #
    cB
    wss
    @1
    cB
    wss
    vx
    cA
    wral
    @0
    @2
    cB
    vx
    cA
    rankr1b.1
    rankval4
    sseq1i
    vx
    cA
    @1
    cB
    iunss
    bitr2i
end
