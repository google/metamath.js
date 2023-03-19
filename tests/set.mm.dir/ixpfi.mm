include "cfn.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "ciun.mm"
include "cmap.mm"
include "co.mm"
include "cixp.mm"
include "wss.mm"
include "iunfi.mm"
include "simpl.mm"
include "mapfi.mm"
include "syl2anc.mm"
include "ixpssmap2g.mm"
include "syl.mm"
include "ssfi.mm"

theorem ixpfi
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  assert |- ( ( A e. Fin /\ A. x e. A B e. Fin ) -> X_ x e. A B e. Fin )

  proof
    cA
    cfn
    wcel
    #
    cB
    cfn
    wcel
    vx
    cA
    wral
    #
    wa
    #
    vx
    cA
    cB
    ciun
    #
    cA
    cmap
    co
    #
    cfn
    wcel
    #
    vx
    cA
    cB
    cixp
    #
    @4
    wss
    #
    @6
    cfn
    wcel
    @2
    @3
    cfn
    wcel
    #
    @0
    @5
    vx
    cA
    cB
    iunfi
    #
    @0
    @1
    simpl
    @3
    cA
    mapfi
    syl2anc
    @2
    @8
    @7
    @9
    vx
    cA
    cB
    cfn
    ixpssmap2g
    syl
    @4
    @6
    ssfi
    syl2anc
end
