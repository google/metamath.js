include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "wex.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "cin.mm"
include "wceq.mm"
include "n0.mm"
include "biimpi.mm"
include "anim2i.mm"
include "zfregcl.mm"
include "imp.mm"
include "disj.mm"
include "rexbii.mm"
include "biimpri.mm"
include "3syl.mm"

theorem zfreg
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( ( A e. V /\ A =/= (/) ) -> E. x e. A ( x i^i A ) = (/) )

  proof
    cA
    cV
    wcel
    #
    cA
    c0
    wne
    #
    wa
    @0
    vx
    cv
    #
    cA
    wcel
    vx
    wex
    #
    wa
    vy
    cv
    cA
    wcel
    wn
    vy
    @2
    wral
    #
    vx
    cA
    wrex
    #
    @2
    cA
    cin
    c0
    wceq
    #
    vx
    cA
    wrex
    #
    @1
    @3
    @0
    @1
    @3
    vx
    cA
    n0
    biimpi
    anim2i
    @0
    @3
    @5
    vx
    vy
    cA
    cV
    zfregcl
    imp
    @7
    @5
    @6
    @4
    vx
    cA
    vy
    @2
    cA
    disj
    rexbii
    biimpri
    3syl
end
