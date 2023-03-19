include "crn.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "cres.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "ccom.mm"
include "wcel.mm"
include "wb.mm"
include "vex.mm"
include "brelrn.mm"
include "ssel.mm"
include "brres.mm"
include "rbaib.mm"
include "syl56.mm"
include "pm5.32d.mm"
include "exbidv.mm"
include "opabbidv.mm"
include "df-co.mm"
include "3eqtr4g.mm"

theorem cores
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ran B C_ C -> ( ( A |` C ) o. B ) = ( A o. B ) )

  proof
    cB
    crn
    #
    cC
    wss
    #
    vz
    cv
    #
    vy
    cv
    #
    cB
    wbr
    #
    @3
    vx
    cv
    #
    cA
    cC
    cres
    #
    wbr
    #
    wa
    #
    vy
    wex
    #
    vz
    vx
    copab
    @4
    @3
    @5
    cA
    wbr
    #
    wa
    #
    vy
    wex
    #
    vz
    vx
    copab
    @6
    cB
    ccom
    cA
    cB
    ccom
    @1
    @9
    @12
    vz
    vx
    @1
    @8
    @11
    vy
    @1
    @4
    @7
    @10
    @4
    @3
    @0
    wcel
    @1
    @3
    cC
    wcel
    #
    @7
    @10
    wb
    @2
    @3
    cB
    vz
    vex
    vy
    vex
    brelrn
    @0
    cC
    @3
    ssel
    @7
    @10
    @13
    @3
    @5
    cA
    cC
    vx
    vex
    brres
    rbaib
    syl56
    pm5.32d
    exbidv
    opabbidv
    vz
    vx
    vy
    @6
    cB
    df-co
    vz
    vx
    vy
    cA
    cB
    df-co
    3eqtr4g
end
