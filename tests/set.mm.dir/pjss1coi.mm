include "wss.mm"
include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "cv.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "pjcoi.mm"
include "adantl.mm"
include "cch.mm"
include "pjcli.mm"
include "ssel2.mm"
include "sylan2.mm"
include "pjid.mm"
include "sylancr.mm"
include "eqtrd.mm"
include "ralrimiva.mm"
include "pjfi.mm"
include "hocofi.mm"
include "hoeqi.mm"
include "sylib.mm"
include "crn.mm"
include "rneq.mm"
include "rncoss.mm"
include "syl6eqssr.mm"
include "pjrni.mm"
include "3sstr3g.mm"
include "impbii.mm"

theorem pjss1coi
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjco.1: |- G e. CH
  assume pjco.2: |- H e. CH


  assert |- ( G C_ H <-> ( ( projh ` H ) o. ( projh ` G ) ) = ( projh ` G ) )

  proof
    cG
    cH
    wss
    #
    cH
    cpjh
    cfv
    #
    cG
    cpjh
    cfv
    #
    ccom
    #
    @2
    wceq
    #
    @0
    vx
    cv
    #
    @3
    cfv
    #
    @5
    @2
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    @4
    @0
    @8
    vx
    chil
    @0
    @5
    chil
    wcel
    #
    wa
    #
    @6
    @7
    @1
    cfv
    #
    @7
    @9
    @6
    @11
    wceq
    @0
    @5
    cH
    cG
    pjco.2
    pjco.1
    pjcoi
    adantl
    @10
    cH
    cch
    wcel
    @7
    cH
    wcel
    #
    @11
    @7
    wceq
    pjco.2
    @9
    @0
    @7
    cG
    wcel
    @12
    @5
    cG
    pjco.1
    pjcli
    cG
    cH
    @7
    ssel2
    sylan2
    @7
    cH
    pjid
    sylancr
    eqtrd
    ralrimiva
    vx
    @3
    @2
    @1
    @2
    cH
    pjco.2
    pjfi
    cG
    pjco.1
    pjfi
    #
    hocofi
    @13
    hoeqi
    sylib
    @4
    @2
    crn
    #
    @1
    crn
    #
    cG
    cH
    @4
    @14
    @3
    crn
    @15
    @3
    @2
    rneq
    @1
    @2
    rncoss
    syl6eqssr
    cG
    pjco.1
    pjrni
    cH
    pjco.2
    pjrni
    3sstr3g
    impbii
end
