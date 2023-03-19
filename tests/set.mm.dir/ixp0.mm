include "c0.mm"
include "wceq.mm"
include "wrex.mm"
include "wne.mm"
include "wral.mm"
include "wn.mm"
include "cixp.mm"
include "nne.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitr3i.mm"
include "ixpn0.mm"
include "necon1bi.mm"
include "sylbi.mm"

theorem ixp0
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f


  assert |- ( E. x e. A B = (/) -> X_ x e. A B = (/) )

  proof
    cB
    c0
    wceq
    #
    vx
    cA
    wrex
    #
    cB
    c0
    wne
    #
    vx
    cA
    wral
    #
    wn
    #
    vx
    cA
    cB
    cixp
    #
    c0
    wceq
    @1
    @2
    wn
    #
    vx
    cA
    wrex
    @4
    @6
    @0
    vx
    cA
    cB
    c0
    nne
    rexbii
    @2
    vx
    cA
    rexnal
    bitr3i
    @3
    @5
    c0
    vx
    cA
    cB
    ixpn0
    necon1bi
    sylbi
end
