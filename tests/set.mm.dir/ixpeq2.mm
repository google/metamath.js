include "wss.mm"
include "wral.mm"
include "wa.mm"
include "cixp.mm"
include "wceq.mm"
include "ss2ixp.mm"
include "anim12i.mm"
include "eqss.mm"
include "ralbii.mm"
include "r19.26.mm"
include "bitri.mm"
include "3imtr4i.mm"

theorem ixpeq2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A. x e. A B = C -> X_ x e. A B = X_ x e. A C )

  proof
    cB
    cC
    wss
    #
    vx
    cA
    wral
    #
    cC
    cB
    wss
    #
    vx
    cA
    wral
    #
    wa
    #
    vx
    cA
    cB
    cixp
    #
    vx
    cA
    cC
    cixp
    #
    wss
    #
    @6
    @5
    wss
    #
    wa
    cB
    cC
    wceq
    #
    vx
    cA
    wral
    #
    @5
    @6
    wceq
    @1
    @7
    @3
    @8
    vx
    cA
    cB
    cC
    ss2ixp
    vx
    cA
    cC
    cB
    ss2ixp
    anim12i
    @10
    @0
    @2
    wa
    #
    vx
    cA
    wral
    @4
    @9
    @11
    vx
    cA
    cB
    cC
    eqss
    ralbii
    @0
    @2
    vx
    cA
    r19.26
    bitri
    @5
    @6
    eqss
    3imtr4i
end
