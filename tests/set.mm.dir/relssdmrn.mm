include "wrel.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "id.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wi.mm"
include "wex.mm"
include "19.8a.mm"
include "wa.mm"
include "opelxp.mm"
include "vex.mm"
include "eldm2.mm"
include "elrn2.mm"
include "anbi12i.mm"
include "bitri.mm"
include "sylanbrc.mm"
include "a1i.mm"
include "relssdv.mm"

theorem relssdmrn
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( Rel A -> A C_ ( dom A X. ran A ) )

  proof
    cA
    wrel
    #
    vx
    vy
    cA
    cA
    cdm
    #
    cA
    crn
    #
    cxp
    #
    @0
    id
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cA
    wcel
    #
    @6
    @3
    wcel
    #
    wi
    @0
    @7
    @7
    vy
    wex
    #
    @7
    vx
    wex
    #
    @8
    @7
    vy
    19.8a
    @7
    vx
    19.8a
    @8
    @4
    @1
    wcel
    #
    @5
    @2
    wcel
    #
    wa
    @9
    @10
    wa
    @4
    @5
    @1
    @2
    opelxp
    @11
    @9
    @12
    @10
    vy
    @4
    cA
    vx
    vex
    eldm2
    vx
    @5
    cA
    vy
    vex
    elrn2
    anbi12i
    bitri
    sylanbrc
    a1i
    relssdv
end
