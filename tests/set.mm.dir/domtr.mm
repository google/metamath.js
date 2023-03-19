include "cdom.mm"
include "reldom.mm"
include "cv.mm"
include "wbr.mm"
include "wf1.mm"
include "wex.mm"
include "vex.mm"
include "brdom.mm"
include "wa.mm"
include "eeanv.mm"
include "ccom.mm"
include "f1co.mm"
include "ancoms.mm"
include "coex.mm"
include "f1eq1.mm"
include "spcev.mm"
include "syl.mm"
include "sylibr.mm"
include "exlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"
include "vtoclr.mm"

theorem domtr
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h


  assert |- ( ( A ~<_ B /\ B ~<_ C ) -> A ~<_ C )

  proof
    vx
    vy
    vz
    cA
    cB
    cC
    cdom
    reldom
    vx
    cv
    #
    vy
    cv
    #
    cdom
    wbr
    @0
    @1
    vg
    cv
    #
    wf1
    #
    vg
    wex
    #
    @1
    vz
    cv
    #
    vf
    cv
    #
    wf1
    #
    vf
    wex
    #
    @0
    @5
    cdom
    wbr
    #
    @1
    @5
    cdom
    wbr
    @0
    @1
    vg
    vy
    vex
    brdom
    @1
    @5
    vf
    vz
    vex
    #
    brdom
    @4
    @8
    wa
    @3
    @7
    wa
    #
    vf
    wex
    vg
    wex
    @9
    @3
    @7
    vg
    vf
    eeanv
    @11
    @9
    vg
    vf
    @11
    @0
    @5
    vh
    cv
    #
    wf1
    #
    vh
    wex
    #
    @9
    @11
    @0
    @5
    @6
    @2
    ccom
    #
    wf1
    #
    @14
    @7
    @3
    @16
    @0
    @1
    @5
    @6
    @2
    f1co
    ancoms
    @13
    @16
    vh
    @15
    @6
    @2
    vf
    vex
    vg
    vex
    coex
    @0
    @5
    @12
    @15
    f1eq1
    spcev
    syl
    @0
    @5
    vh
    @10
    brdom
    sylibr
    exlimivv
    sylbir
    syl2anb
    vtoclr
end
