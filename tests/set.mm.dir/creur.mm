include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cr.mm"
include "wrex.mm"
include "wreu.mm"
include "cnre.mm"
include "wa.mm"
include "wb.mm"
include "wral.mm"
include "cru.mm"
include "ancoms.mm"
include "eqcom.mm"
include "ancom.mm"
include "3bitr4g.mm"
include "anassrs.mm"
include "rexbidva.mm"
include "biidd.mm"
include "ceqsrexv.mm"
include "ad2antlr.mm"
include "bitrd.mm"
include "ralrimiva.mm"
include "reu6i.mm"
include "syldan.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "reubidv.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "syl.mm"

theorem creur
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A z
  disjoint A w
  assert |- ( A e. CC -> E! x e. RR E. y e. RR A = ( x + ( _i x. y ) ) )

  proof
    cA
    cc
    wcel
    cA
    vz
    cv
    #
    ci
    vw
    cv
    #
    cmul
    co
    caddc
    co
    #
    wceq
    #
    vw
    cr
    wrex
    vz
    cr
    wrex
    cA
    vx
    cv
    #
    ci
    vy
    cv
    #
    cmul
    co
    caddc
    co
    #
    wceq
    #
    vy
    cr
    wrex
    #
    vx
    cr
    wreu
    #
    vz
    vw
    cA
    cnre
    @3
    @9
    vz
    vw
    cr
    cr
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    wa
    #
    @9
    @3
    @2
    @6
    wceq
    #
    vy
    cr
    wrex
    #
    vx
    cr
    wreu
    #
    @10
    @11
    @14
    @4
    @0
    wceq
    #
    wb
    #
    vx
    cr
    wral
    @15
    @12
    @17
    vx
    cr
    @12
    @4
    cr
    wcel
    #
    wa
    #
    @14
    @5
    @1
    wceq
    #
    @16
    wa
    #
    vy
    cr
    wrex
    #
    @16
    @19
    @13
    @21
    vy
    cr
    @12
    @18
    @5
    cr
    wcel
    #
    @13
    @21
    wb
    @12
    @18
    @23
    wa
    #
    wa
    @6
    @2
    wceq
    #
    @16
    @20
    wa
    #
    @13
    @21
    @24
    @12
    @25
    @26
    wb
    @4
    @5
    @0
    @1
    cru
    ancoms
    @2
    @6
    eqcom
    @20
    @16
    ancom
    3bitr4g
    anassrs
    rexbidva
    @11
    @22
    @16
    wb
    @10
    @18
    @16
    @16
    vy
    @1
    cr
    @20
    @16
    biidd
    ceqsrexv
    ad2antlr
    bitrd
    ralrimiva
    @14
    vx
    cr
    @0
    reu6i
    syldan
    @3
    @8
    @14
    vx
    cr
    @3
    @7
    @13
    vy
    cr
    cA
    @2
    @6
    eqeq1
    rexbidv
    reubidv
    syl5ibrcom
    rexlimivv
    syl
end
