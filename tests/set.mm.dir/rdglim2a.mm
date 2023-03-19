include "wcel.mm"
include "wlim.mm"
include "wa.mm"
include "crdg.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cuni.mm"
include "ciun.mm"
include "rdglim2.mm"
include "fvex.mm"
include "dfiun2.mm"
include "syl6eqr.mm"

theorem rdglim2a
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F y
  assert |- ( ( B e. C /\ Lim B ) -> ( rec ( F , A ) ` B ) = U_ x e. B ( rec ( F , A ) ` x ) )

  proof
    cB
    cC
    wcel
    cB
    wlim
    wa
    cB
    cF
    cA
    crdg
    #
    cfv
    vy
    cv
    vx
    cv
    #
    @0
    cfv
    #
    wceq
    vx
    cB
    wrex
    vy
    cab
    cuni
    vx
    cB
    @2
    ciun
    vx
    vy
    cA
    cB
    cC
    cF
    rdglim2
    vx
    vy
    cB
    @2
    @1
    @0
    fvex
    dfiun2
    syl6eqr
end
