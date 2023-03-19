include "cpw.mm"
include "wss.mm"
include "cuni.mm"
include "cv.mm"
include "wral.mm"
include "sspwuni.mm"
include "unissb.mm"
include "bitri.mm"

theorem pwssb
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A C_ ~P B <-> A. x e. A x C_ B )

  proof
    cA
    cB
    cpw
    wss
    cA
    cuni
    cB
    wss
    vx
    cv
    cB
    wss
    vx
    cA
    wral
    cA
    cB
    sspwuni
    vx
    cA
    cB
    unissb
    bitri
end
