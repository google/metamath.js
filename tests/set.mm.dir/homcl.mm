include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "w3a.mm"
include "chot.mm"
include "co.mm"
include "cfv.mm"
include "csm.mm"
include "homval.mm"
include "wa.mm"
include "ffvelrn.mm"
include "anim2i.mm"
include "3impb.mm"
include "hvmulcl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem homcl
  let cA: class A
  let cB: class B
  let cT: class T


  assert |- ( ( A e. CC /\ T : ~H --> ~H /\ B e. ~H ) -> ( ( A .op T ) ` B ) e. ~H )

  proof
    cA
    cc
    wcel
    #
    chil
    chil
    cT
    wf
    #
    cB
    chil
    wcel
    #
    w3a
    #
    cB
    cA
    cT
    chot
    co
    cfv
    cA
    cB
    cT
    cfv
    #
    csm
    co
    #
    chil
    cA
    cB
    cT
    homval
    @3
    @0
    @4
    chil
    wcel
    #
    wa
    #
    @5
    chil
    wcel
    @0
    @1
    @2
    @7
    @1
    @2
    wa
    @6
    @0
    chil
    chil
    cB
    cT
    ffvelrn
    anim2i
    3impb
    cA
    @4
    hvmulcl
    syl
    eqeltrd
end
