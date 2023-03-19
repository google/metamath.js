include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "ciun.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cuni.mm"
include "cvv.mm"
include "dfiun2g.mm"
include "adantl.mm"
include "abrexexg.mm"
include "uniexg.mm"
include "syl.mm"
include "adantr.mm"
include "eqeltrd.mm"

theorem iunexg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ( A e. V /\ A. x e. A B e. W ) -> U_ x e. A B e. _V )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
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
    cvv
    @1
    @2
    @4
    wceq
    @0
    vx
    vy
    cA
    cB
    cW
    dfiun2g
    adantl
    @0
    @4
    cvv
    wcel
    #
    @1
    @0
    @3
    cvv
    wcel
    @5
    vx
    vy
    cA
    cB
    cV
    abrexexg
    @3
    cvv
    uniexg
    syl
    adantr
    eqeltrd
end
