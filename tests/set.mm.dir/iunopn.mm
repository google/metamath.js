include "ctop.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "ciun.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cuni.mm"
include "dfiun2g.mm"
include "adantl.mm"
include "wss.mm"
include "uniiunlem.mm"
include "ibi.mm"
include "uniopn.mm"
include "sylan2.mm"
include "eqeltrd.mm"

theorem iunopn
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cJ: class J
  let vy: setvar y

  disjoint A x
  disjoint J x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint J y
  assert |- ( ( J e. Top /\ A. x e. A B e. J ) -> U_ x e. A B e. J )

  proof
    cJ
    ctop
    wcel
    #
    cB
    cJ
    wcel
    vx
    cA
    wral
    #
    wa
    vx
    cA
    cB
    ciun
    #
    vy
    cv
    cB
    wceq
    vx
    cA
    wrex
    vy
    cab
    #
    cuni
    #
    cJ
    @1
    @2
    @4
    wceq
    @0
    vx
    vy
    cA
    cB
    cJ
    dfiun2g
    adantl
    @1
    @0
    @3
    cJ
    wss
    #
    @4
    cJ
    wcel
    @1
    @5
    vx
    vy
    cA
    cB
    cJ
    cJ
    uniiunlem
    ibi
    @3
    cJ
    uniopn
    sylan2
    eqeltrd
end
