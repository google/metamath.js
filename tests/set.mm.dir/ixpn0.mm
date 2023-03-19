include "cixp.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wral.mm"
include "n0.mm"
include "cab.mm"
include "wfn.mm"
include "cfv.mm"
include "wa.mm"
include "df-ixp.mm"
include "abeq2i.mm"
include "ne0i.mm"
include "ralimi.mm"
include "simplbiim.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem ixpn0
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f


  assert |- ( X_ x e. A B =/= (/) -> A. x e. A B =/= (/) )

  proof
    vx
    cA
    cB
    cixp
    #
    c0
    wne
    vf
    cv
    #
    @0
    wcel
    #
    vf
    wex
    cB
    c0
    wne
    #
    vx
    cA
    wral
    #
    vf
    @0
    n0
    @2
    @4
    vf
    @2
    @1
    vx
    cv
    #
    cA
    wcel
    vx
    cab
    wfn
    #
    @5
    @1
    cfv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    #
    @4
    @6
    @9
    wa
    vf
    @0
    vx
    cA
    cB
    vf
    df-ixp
    abeq2i
    @8
    @3
    vx
    cA
    cB
    @7
    ne0i
    ralimi
    simplbiim
    exlimiv
    sylbi
end
