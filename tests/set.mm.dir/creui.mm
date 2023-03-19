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
include "simpr.mm"
include "eqcom.mm"
include "cru.mm"
include "ancoms.mm"
include "syl5bb.mm"
include "anass1rs.mm"
include "rexbidva.mm"
include "biidd.mm"
include "ceqsrexv.mm"
include "ad2antrr.mm"
include "bitrd.mm"
include "ralrimiva.mm"
include "reu6i.mm"
include "syl2anc.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "reubidv.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "syl.mm"

theorem creui
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
  assert |- ( A e. CC -> E! y e. RR E. x e. RR A = ( x + ( _i x. y ) ) )

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
    vx
    cr
    wrex
    #
    vy
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
    vx
    cr
    wrex
    #
    vy
    cr
    wreu
    #
    @12
    @11
    @14
    @5
    @1
    wceq
    #
    wb
    #
    vy
    cr
    wral
    @15
    @10
    @11
    simpr
    @12
    @17
    vy
    cr
    @12
    @5
    cr
    wcel
    #
    wa
    #
    @14
    @4
    @0
    wceq
    #
    @16
    wa
    #
    vx
    cr
    wrex
    #
    @16
    @19
    @13
    @21
    vx
    cr
    @12
    @4
    cr
    wcel
    #
    @18
    @13
    @21
    wb
    @13
    @6
    @2
    wceq
    #
    @12
    @23
    @18
    wa
    #
    wa
    @21
    @2
    @6
    eqcom
    @25
    @12
    @24
    @21
    wb
    @4
    @5
    @0
    @1
    cru
    ancoms
    syl5bb
    anass1rs
    rexbidva
    @10
    @22
    @16
    wb
    @11
    @18
    @16
    @16
    vx
    @0
    cr
    @20
    @16
    biidd
    ceqsrexv
    ad2antrr
    bitrd
    ralrimiva
    @14
    vy
    cr
    @1
    reu6i
    syl2anc
    @3
    @8
    @14
    vy
    cr
    @3
    @7
    @13
    vx
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
