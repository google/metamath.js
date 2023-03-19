include "wcel.mm"
include "cixp.mm"
include "cmap.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wf.mm"
include "cab.mm"
include "mapvalg.mm"
include "vex.mm"
include "elixpconst.mm"
include "abbi2i.mm"
include "syl6reqr.mm"
include "ancoms.mm"

theorem ixpconstg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vf: setvar f

  disjoint A x
  disjoint B x
  disjoint f x
  disjoint A f
  disjoint B f
  assert |- ( ( A e. V /\ B e. W ) -> X_ x e. A B = ( B ^m A ) )

  proof
    cB
    cW
    wcel
    #
    cA
    cV
    wcel
    #
    vx
    cA
    cB
    cixp
    #
    cB
    cA
    cmap
    co
    #
    wceq
    @0
    @1
    wa
    @3
    cA
    cB
    vf
    cv
    #
    wf
    #
    vf
    cab
    @2
    cB
    cA
    cW
    cV
    vf
    mapvalg
    @5
    vf
    @2
    vx
    cA
    cB
    @4
    vf
    vex
    elixpconst
    abbi2i
    syl6reqr
    ancoms
end
