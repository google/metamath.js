include "chil.mm"
include "wf.mm"
include "wcel.mm"
include "chod.mm"
include "co.mm"
include "cfv.mm"
include "w3a.mm"
include "cmv.mm"
include "hodval.mm"
include "ffvelrn.mm"
include "3adant2.mm"
include "3adant1.mm"
include "hvsubcl.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "3expa.mm"

theorem hodcl
  let cA: class A
  let cS: class S
  let cT: class T


  assert |- ( ( ( S : ~H --> ~H /\ T : ~H --> ~H ) /\ A e. ~H ) -> ( ( S -op T ) ` A ) e. ~H )

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
    cA
    chil
    wcel
    #
    cA
    cS
    cT
    chod
    co
    cfv
    #
    chil
    wcel
    @0
    @1
    @2
    w3a
    #
    @3
    cA
    cS
    cfv
    #
    cA
    cT
    cfv
    #
    cmv
    co
    #
    chil
    cA
    cS
    cT
    hodval
    @4
    @5
    chil
    wcel
    #
    @6
    chil
    wcel
    #
    @7
    chil
    wcel
    @0
    @2
    @8
    @1
    chil
    chil
    cA
    cS
    ffvelrn
    3adant2
    @1
    @2
    @9
    @0
    chil
    chil
    cA
    cT
    ffvelrn
    3adant1
    @5
    @6
    hvsubcl
    syl2anc
    eqeltrd
    3expa
end
