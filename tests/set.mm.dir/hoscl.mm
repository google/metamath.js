include "chil.mm"
include "wf.mm"
include "wa.mm"
include "wcel.mm"
include "chos.mm"
include "co.mm"
include "cfv.mm"
include "cva.mm"
include "wceq.mm"
include "hosval.mm"
include "3expa.mm"
include "ffvelrn.mm"
include "anim12i.mm"
include "anandirs.mm"
include "hvaddcl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem hoscl
  let cA: class A
  let cS: class S
  let cT: class T


  assert |- ( ( ( S : ~H --> ~H /\ T : ~H --> ~H ) /\ A e. ~H ) -> ( ( S +op T ) ` A ) e. ~H )

  proof
    chil
    chil
    cS
    wf
    #
    chil
    chil
    cT
    wf
    #
    wa
    cA
    chil
    wcel
    #
    wa
    #
    cA
    cS
    cT
    chos
    co
    cfv
    #
    cA
    cS
    cfv
    #
    cA
    cT
    cfv
    #
    cva
    co
    #
    chil
    @0
    @1
    @2
    @4
    @7
    wceq
    cA
    cS
    cT
    hosval
    3expa
    @3
    @5
    chil
    wcel
    #
    @6
    chil
    wcel
    #
    wa
    #
    @7
    chil
    wcel
    @0
    @1
    @2
    @10
    @0
    @2
    wa
    @8
    @1
    @2
    wa
    @9
    chil
    chil
    cA
    cS
    ffvelrn
    chil
    chil
    cA
    cT
    ffvelrn
    anim12i
    anandirs
    @5
    @6
    hvaddcl
    syl
    eqeltrd
end
