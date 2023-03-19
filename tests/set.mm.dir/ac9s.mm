include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cixp.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "ac6s4.mm"
include "n0.mm"
include "vex.mm"
include "elixp.mm"
include "exbii.mm"
include "bitr2i.mm"
include "sylib.mm"
include "ixpn0.mm"
include "impbii.mm"

theorem ac9s
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f
  assume ac9.1: |- A e. _V

  disjoint A x
  disjoint f x
  disjoint A f
  disjoint B f
  assert |- ( A. x e. A B =/= (/) <-> X_ x e. A B =/= (/) )

  proof
    cB
    c0
    wne
    vx
    cA
    wral
    #
    vx
    cA
    cB
    cixp
    #
    c0
    wne
    #
    @0
    vf
    cv
    #
    cA
    wfn
    vx
    cv
    @3
    cfv
    cB
    wcel
    vx
    cA
    wral
    wa
    #
    vf
    wex
    #
    @2
    vx
    cA
    cB
    vf
    ac9.1
    ac6s4
    @2
    @3
    @1
    wcel
    #
    vf
    wex
    @5
    vf
    @1
    n0
    @6
    @4
    vf
    vx
    cA
    cB
    @3
    vf
    vex
    elixp
    exbii
    bitr2i
    sylib
    vx
    cA
    cB
    ixpn0
    impbii
end
