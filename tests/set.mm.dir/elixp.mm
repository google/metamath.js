include "cixp.mm"
include "wcel.mm"
include "cvv.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "elixp2.mm"
include "3anass.mm"
include "mpbiran.mm"
include "bitri.mm"

theorem elixp
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume elixp.1: |- F e. _V

  disjoint F x
  disjoint A x
  assert |- ( F e. X_ x e. A B <-> ( F Fn A /\ A. x e. A ( F ` x ) e. B ) )

  proof
    cF
    vx
    cA
    cB
    cixp
    wcel
    cF
    cvv
    wcel
    #
    cF
    cA
    wfn
    #
    vx
    cv
    cF
    cfv
    cB
    wcel
    vx
    cA
    wral
    #
    w3a
    #
    @1
    @2
    wa
    #
    vx
    cA
    cB
    cF
    elixp2
    @3
    @0
    @4
    elixp.1
    @0
    @1
    @2
    3anass
    mpbiran
    bitri
end
