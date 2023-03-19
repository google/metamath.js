include "cv.mm"
include "csn.mm"
include "ciun.mm"
include "cxp.mm"
include "xpiundir.mm"
include "iunid.mm"
include "xpeq1i.mm"
include "eqtr3i.mm"

theorem iunxpconst
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- U_ x e. A ( { x } X. B ) = ( A X. B )

  proof
    vx
    cA
    vx
    cv
    csn
    #
    ciun
    #
    cB
    cxp
    vx
    cA
    @0
    cB
    cxp
    ciun
    cA
    cB
    cxp
    vx
    cA
    @0
    cB
    xpiundir
    @1
    cA
    cB
    vx
    cA
    iunid
    xpeq1i
    eqtr3i
end
