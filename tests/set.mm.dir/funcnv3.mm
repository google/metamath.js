include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "crn.mm"
include "wral.mm"
include "wex.mm"
include "wa.mm"
include "ccnv.mm"
include "wfun.mm"
include "cdm.mm"
include "wreu.mm"
include "wcel.mm"
include "dfrn2.mm"
include "abeq2i.mm"
include "biimpi.mm"
include "biantrurd.mm"
include "ralbiia.mm"
include "funcnv.mm"
include "weu.mm"
include "df-reu.mm"
include "vex.mm"
include "breldm.mm"
include "pm4.71ri.mm"
include "eubii.mm"
include "eu5.mm"
include "3bitr2i.mm"
include "ralbii.mm"
include "3bitr4i.mm"

theorem funcnv3
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( Fun `' A <-> A. y e. ran A E! x e. dom A x A y )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cA
    wbr
    #
    vx
    wmo
    #
    vy
    cA
    crn
    #
    wral
    @2
    vx
    wex
    #
    @3
    wa
    #
    vy
    @4
    wral
    cA
    ccnv
    wfun
    @2
    vx
    cA
    cdm
    #
    wreu
    #
    vy
    @4
    wral
    @3
    @6
    vy
    @4
    @1
    @4
    wcel
    #
    @5
    @3
    @9
    @5
    @5
    vy
    @4
    vx
    vy
    cA
    dfrn2
    abeq2i
    biimpi
    biantrurd
    ralbiia
    vx
    vy
    cA
    funcnv
    @8
    @6
    vy
    @4
    @8
    @0
    @7
    wcel
    #
    @2
    wa
    #
    vx
    weu
    @2
    vx
    weu
    @6
    @2
    vx
    @7
    df-reu
    @2
    @11
    vx
    @2
    @10
    @0
    @1
    cA
    vx
    vex
    vy
    vex
    breldm
    pm4.71ri
    eubii
    @2
    vx
    eu5
    3bitr2i
    ralbii
    3bitr4i
end
