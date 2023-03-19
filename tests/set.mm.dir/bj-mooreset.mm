include "cuni.mm"
include "cv.mm"
include "cint.mm"
include "cin.mm"
include "wcel.mm"
include "cpw.mm"
include "wral.mm"
include "cvv.mm"
include "c0.mm"
include "wi.mm"
include "0elpw.mm"
include "wceq.mm"
include "rint0.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "uniexr.mm"
include "syl.mm"

theorem bj-mooreset
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A. x e. ~P A ( U. A i^i |^| x ) e. A -> A e. _V )

  proof
    cA
    cuni
    #
    vx
    cv
    #
    cint
    cin
    #
    cA
    wcel
    #
    vx
    cA
    cpw
    #
    wral
    #
    @0
    cA
    wcel
    #
    cA
    cvv
    wcel
    c0
    @4
    wcel
    @5
    @6
    wi
    cA
    0elpw
    @3
    @6
    vx
    c0
    @4
    @1
    c0
    wceq
    @2
    @0
    cA
    @0
    @1
    rint0
    eleq1d
    rspcv
    ax-mp
    cA
    cA
    uniexr
    syl
end
