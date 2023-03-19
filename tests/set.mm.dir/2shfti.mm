include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cshi.mm"
include "wbr.mm"
include "copab.mm"
include "caddc.mm"
include "wb.mm"
include "shftfval.mm"
include "breqd.mm"
include "ovex.mm"
include "vex.mm"
include "wceq.mm"
include "eleq1.mm"
include "oveq1.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "breq2.mm"
include "anbi2d.mm"
include "eqid.mm"
include "brab.mm"
include "syl6bb.mm"
include "ad2antrr.mm"
include "subcl.mm"
include "biantrurd.mm"
include "ancoms.mm"
include "adantll.mm"
include "w3a.mm"
include "sub32.mm"
include "subsub4.mm"
include "eqtr3d.mm"
include "3expb.mm"
include "3bitr2d.mm"
include "pm5.32da.mm"
include "opabbidv.mm"
include "adantl.mm"
include "addcl.mm"
include "syl.mm"
include "3eqtr4d.mm"

theorem 2shfti
  let cA: class A
  let cB: class B
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  assume shftfval.1: |- F e. _V


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( F shift A ) shift B ) = ( F shift ( A + B ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    vx
    cv
    #
    cc
    wcel
    #
    @3
    cB
    cmin
    co
    #
    vy
    cv
    #
    cF
    cA
    cshi
    co
    #
    wbr
    #
    wa
    #
    vx
    vy
    copab
    #
    @4
    @3
    cA
    cB
    caddc
    co
    #
    cmin
    co
    #
    @6
    cF
    wbr
    #
    wa
    #
    vx
    vy
    copab
    #
    @7
    cB
    cshi
    co
    #
    cF
    @11
    cshi
    co
    #
    @2
    @9
    @14
    vx
    vy
    @2
    @4
    @8
    @13
    @2
    @4
    wa
    #
    @8
    @5
    cc
    wcel
    #
    @5
    cA
    cmin
    co
    #
    @6
    cF
    wbr
    #
    wa
    #
    @21
    @13
    @0
    @8
    @22
    wb
    @1
    @4
    @0
    @8
    @5
    @6
    vz
    cv
    #
    cc
    wcel
    #
    @23
    cA
    cmin
    co
    #
    vw
    cv
    #
    cF
    wbr
    #
    wa
    #
    vz
    vw
    copab
    #
    wbr
    @22
    @0
    @7
    @29
    @5
    @6
    vz
    vw
    cA
    cF
    shftfval.1
    shftfval
    breqd
    @28
    @19
    @20
    @26
    cF
    wbr
    #
    wa
    @22
    vz
    vw
    @5
    @6
    @29
    @3
    cB
    cmin
    ovex
    vy
    vex
    @23
    @5
    wceq
    #
    @24
    @19
    @27
    @30
    @23
    @5
    cc
    eleq1
    @31
    @25
    @20
    @26
    cF
    @23
    @5
    cA
    cmin
    oveq1
    breq1d
    anbi12d
    @26
    @6
    wceq
    @30
    @21
    @19
    @26
    @6
    @20
    cF
    breq2
    anbi2d
    @29
    eqid
    brab
    syl6bb
    ad2antrr
    @1
    @4
    @21
    @22
    wb
    #
    @0
    @4
    @1
    @32
    @4
    @1
    wa
    @19
    @21
    @3
    cB
    subcl
    biantrurd
    ancoms
    adantll
    @18
    @20
    @12
    @6
    cF
    @4
    @2
    @20
    @12
    wceq
    #
    @4
    @0
    @1
    @33
    @4
    @0
    @1
    w3a
    @3
    cA
    cmin
    co
    cB
    cmin
    co
    @20
    @12
    @3
    cA
    cB
    sub32
    @3
    cA
    cB
    subsub4
    eqtr3d
    3expb
    ancoms
    breq1d
    3bitr2d
    pm5.32da
    opabbidv
    @1
    @16
    @10
    wceq
    @0
    vx
    vy
    cB
    @7
    cF
    cA
    cshi
    ovex
    shftfval
    adantl
    @2
    @11
    cc
    wcel
    @17
    @15
    wceq
    cA
    cB
    addcl
    vx
    vy
    @11
    cF
    shftfval.1
    shftfval
    syl
    3eqtr4d
end
