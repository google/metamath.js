include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "wbr.mm"
include "wreu.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "wf.mm"
include "dffo4.mm"
include "cxp.mm"
include "wss.mm"
include "dff4.mm"
include "simprbi.mm"
include "anim1i.mm"
include "sylbi.mm"
include "eximi.mm"
include "cin.mm"
include "crn.mm"
include "wceq.mm"
include "wcel.mm"
include "brinxp.mm"
include "reubidva.mm"
include "biimpd.mm"
include "ralimia.mm"
include "inss2.mm"
include "jctil.mm"
include "sylibr.mm"
include "rninxp.mm"
include "biimpri.mm"
include "anim12i.mm"
include "dffo2.mm"
include "vex.mm"
include "inex1.mm"
include "foeq1.mm"
include "spcev.mm"
include "syl.mm"
include "exlimiv.mm"
include "cbvexv.mm"
include "sylib.mm"
include "impbii.mm"

theorem exfo
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let vz: setvar z
  let cF: class F

  disjoint f x
  disjoint f y
  disjoint A f
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B f
  disjoint B x
  disjoint B y
  disjoint f g
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B g
  disjoint B z
  disjoint F x
  disjoint F y
  disjoint F z
  assert |- ( E. f f : A -onto-> B <-> E. f ( A. x e. A E! y e. B x f y /\ A. x e. B E. y e. A y f x ) )

  proof
    cA
    cB
    vf
    cv
    #
    wfo
    #
    vf
    wex
    #
    vx
    cv
    #
    vy
    cv
    #
    @0
    wbr
    #
    vy
    cB
    wreu
    #
    vx
    cA
    wral
    #
    @4
    @3
    @0
    wbr
    vy
    cA
    wrex
    vx
    cB
    wral
    #
    wa
    #
    vf
    wex
    #
    @1
    @9
    vf
    @1
    cA
    cB
    @0
    wf
    #
    @8
    wa
    @9
    vy
    vx
    cA
    cB
    @0
    dffo4
    @11
    @7
    @8
    @11
    @0
    cA
    cB
    cxp
    #
    wss
    @7
    vx
    vy
    cA
    cB
    @0
    dff4
    simprbi
    anim1i
    sylbi
    eximi
    @10
    cA
    cB
    vg
    cv
    #
    wfo
    #
    vg
    wex
    #
    @2
    @9
    @15
    vf
    @9
    cA
    cB
    @0
    @12
    cin
    #
    wfo
    #
    @15
    @9
    cA
    cB
    @16
    wf
    #
    @16
    crn
    cB
    wceq
    #
    wa
    @17
    @7
    @18
    @8
    @19
    @7
    @16
    @12
    wss
    #
    @3
    @4
    @16
    wbr
    #
    vy
    cB
    wreu
    #
    vx
    cA
    wral
    #
    wa
    @18
    @7
    @23
    @20
    @6
    @22
    vx
    cA
    @3
    cA
    wcel
    #
    @6
    @22
    @24
    @5
    @21
    vy
    cB
    @3
    @4
    cA
    cB
    @0
    brinxp
    reubidva
    biimpd
    ralimia
    @0
    @12
    inss2
    jctil
    vx
    vy
    cA
    cB
    @16
    dff4
    sylibr
    @19
    @8
    vy
    vx
    cA
    cB
    @0
    rninxp
    biimpri
    anim12i
    cA
    cB
    @16
    dffo2
    sylibr
    @14
    @17
    vg
    @16
    @0
    @12
    vf
    vex
    inex1
    cA
    cB
    @13
    @16
    foeq1
    spcev
    syl
    exlimiv
    @14
    @1
    vg
    vf
    cA
    cB
    @13
    @0
    foeq1
    cbvexv
    sylib
    impbii
end
