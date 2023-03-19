include "crn.mm"
include "cdm.mm"
include "wss.mm"
include "ccom.mm"
include "dmcoss.mm"
include "a1i.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "ssel.mm"
include "vex.mm"
include "elrn.mm"
include "eldm.mm"
include "imbi12i.mm"
include "19.8a.mm"
include "imim1i.mm"
include "pm3.2.mm"
include "eximdv.mm"
include "sylcom.mm"
include "sylbi.mm"
include "syl.mm"
include "excom.mm"
include "syl6ibr.mm"
include "opelco.mm"
include "exbii.mm"
include "eldm2.mm"
include "3imtr4g.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem dmcosseq
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ran B C_ dom A -> dom ( A o. B ) = dom B )

  proof
    cB
    crn
    #
    cA
    cdm
    #
    wss
    #
    cA
    cB
    ccom
    #
    cdm
    #
    cB
    cdm
    #
    @4
    @5
    wss
    @2
    cA
    cB
    dmcoss
    a1i
    @2
    vx
    @5
    @4
    @2
    vx
    cv
    #
    vy
    cv
    #
    cB
    wbr
    #
    vy
    wex
    #
    @6
    vz
    cv
    #
    cop
    @3
    wcel
    #
    vz
    wex
    #
    @6
    @5
    wcel
    @6
    @4
    wcel
    @2
    @9
    @8
    @7
    @10
    cA
    wbr
    #
    wa
    #
    vy
    wex
    #
    vz
    wex
    #
    @12
    @2
    @9
    @14
    vz
    wex
    #
    vy
    wex
    @16
    @2
    @8
    @17
    vy
    @2
    @7
    @0
    wcel
    #
    @7
    @1
    wcel
    #
    wi
    #
    @8
    @17
    wi
    #
    @0
    @1
    @7
    ssel
    @20
    @8
    vx
    wex
    #
    @13
    vz
    wex
    #
    wi
    #
    @21
    @18
    @22
    @19
    @23
    vx
    @7
    cB
    vy
    vex
    #
    elrn
    vz
    @7
    cA
    @25
    eldm
    imbi12i
    @24
    @8
    @23
    @17
    @8
    @22
    @23
    @8
    vx
    19.8a
    imim1i
    @8
    @13
    @14
    vz
    @8
    @13
    pm3.2
    eximdv
    sylcom
    sylbi
    syl
    eximdv
    @14
    vz
    vy
    excom
    syl6ibr
    @11
    @15
    vz
    vy
    @6
    @10
    cA
    cB
    vx
    vex
    #
    vz
    vex
    opelco
    exbii
    syl6ibr
    vy
    @6
    cB
    @26
    eldm
    vz
    @6
    @3
    @26
    eldm2
    3imtr4g
    ssrdv
    eqssd
end
