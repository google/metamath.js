include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wf.mm"
include "cab.mm"
include "cvv.mm"
include "cmap.mm"
include "co.mm"
include "wceq.mm"
include "mapex.mm"
include "ancoms.mm"
include "wi.mm"
include "elex.mm"
include "feq3.mm"
include "abbidv.mm"
include "feq2.mm"
include "df-map.mm"
include "ovmpt2g.mm"
include "3expia.mm"
include "syl2an.mm"
include "mpd.mm"

theorem mapvalg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y

  disjoint A f
  disjoint B f
  disjoint x y
  disjoint f x
  disjoint A x
  disjoint f y
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( ( A e. C /\ B e. D ) -> ( A ^m B ) = { f | f : B --> A } )

  proof
    cA
    cC
    wcel
    #
    cB
    cD
    wcel
    #
    wa
    cB
    cA
    vf
    cv
    #
    wf
    #
    vf
    cab
    #
    cvv
    wcel
    #
    cA
    cB
    cmap
    co
    @4
    wceq
    #
    @1
    @0
    @5
    cB
    cA
    cD
    cC
    vf
    mapex
    ancoms
    @0
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    @5
    @6
    wi
    @1
    cA
    cC
    elex
    cB
    cD
    elex
    @7
    @8
    @5
    @6
    vx
    vy
    cA
    cB
    cvv
    cvv
    vy
    cv
    #
    vx
    cv
    #
    @2
    wf
    #
    vf
    cab
    @4
    cmap
    @9
    cA
    @2
    wf
    #
    vf
    cab
    cvv
    @10
    cA
    wceq
    @11
    @12
    vf
    @10
    cA
    @9
    @2
    feq3
    abbidv
    @9
    cB
    wceq
    @12
    @3
    vf
    @9
    cB
    cA
    @2
    feq2
    abbidv
    vx
    vy
    vf
    df-map
    ovmpt2g
    3expia
    syl2an
    mpd
end
