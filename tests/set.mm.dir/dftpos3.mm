include "cdm.mm"
include "wrel.mm"
include "ctpos.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "coprab.mm"
include "wcel.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "ccnv.mm"
include "relcnv.mm"
include "dmtpos.mm"
include "releqd.mm"
include "mpbiri.mm"
include "reltpos.mm"
include "jctil.mm"
include "relrelss.mm"
include "sylib.mm"
include "sseld.mm"
include "elvvv.mm"
include "syl6ib.mm"
include "pm4.71rd.mm"
include "19.41vvv.mm"
include "eleq1.mm"
include "df-br.mm"
include "wb.mm"
include "vex.mm"
include "brtpos.mm"
include "ax-mp.mm"
include "bitr3i.mm"
include "syl6bb.mm"
include "pm5.32i.mm"
include "3exbii.mm"
include "abbi2dv.mm"
include "df-oprab.mm"
include "syl6eqr.mm"

theorem dftpos3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cA: class A
  let cB: class B
  let vw: setvar w
  let cG: class G

  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint G x
  assert |- ( Rel dom F -> tpos F = { <. <. x , y >. , z >. | <. y , x >. F z } )

  proof
    cF
    cdm
    #
    wrel
    #
    cF
    ctpos
    #
    vw
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    vz
    cv
    #
    cop
    #
    wceq
    #
    @5
    @4
    cop
    @7
    cF
    wbr
    #
    wa
    #
    vz
    wex
    vy
    wex
    vx
    wex
    #
    vw
    cab
    @10
    vx
    vy
    vz
    coprab
    @1
    @12
    vw
    @2
    @1
    @3
    @2
    wcel
    #
    @9
    vz
    wex
    vy
    wex
    vx
    wex
    #
    @13
    wa
    #
    @12
    @1
    @13
    @14
    @1
    @13
    @3
    cvv
    cvv
    cxp
    cvv
    cxp
    #
    wcel
    @14
    @1
    @2
    @16
    @3
    @1
    @2
    wrel
    #
    @2
    cdm
    #
    wrel
    #
    wa
    @2
    @16
    wss
    @1
    @19
    @17
    @1
    @19
    @0
    ccnv
    #
    wrel
    @0
    relcnv
    @1
    @18
    @20
    cF
    dmtpos
    releqd
    mpbiri
    cF
    reltpos
    jctil
    @2
    relrelss
    sylib
    sseld
    vx
    vy
    vz
    @3
    elvvv
    syl6ib
    pm4.71rd
    @15
    @9
    @13
    wa
    #
    vz
    wex
    vy
    wex
    vx
    wex
    @12
    @9
    @13
    vx
    vy
    vz
    19.41vvv
    @21
    @11
    vx
    vy
    vz
    @9
    @13
    @10
    @9
    @13
    @8
    @2
    wcel
    #
    @10
    @3
    @8
    @2
    eleq1
    @22
    @6
    @7
    @2
    wbr
    #
    @10
    @6
    @7
    @2
    df-br
    @7
    cvv
    wcel
    @23
    @10
    wb
    vz
    vex
    @4
    @5
    @7
    cF
    cvv
    brtpos
    ax-mp
    bitr3i
    syl6bb
    pm5.32i
    3exbii
    bitr3i
    syl6bb
    abbi2dv
    @10
    vx
    vy
    vz
    vw
    df-oprab
    syl6eqr
end
