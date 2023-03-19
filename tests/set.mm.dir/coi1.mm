include "cid.mm"
include "ccom.mm"
include "wrel.mm"
include "wceq.mm"
include "relco.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "vex.mm"
include "opelco.mm"
include "ideq.mm"
include "equcom.mm"
include "bitri.mm"
include "anbi1i.mm"
include "exbii.mm"
include "breq1.mm"
include "equsexvw.mm"
include "df-br.mm"
include "eqrelriv.mm"
include "mpan.mm"

theorem coi1
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( Rel A -> ( A o. _I ) = A )

  proof
    cA
    cid
    ccom
    #
    wrel
    cA
    wrel
    @0
    cA
    wceq
    cA
    cid
    relco
    vx
    vy
    @0
    cA
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @0
    wcel
    #
    @1
    @2
    cA
    wbr
    #
    @3
    cA
    wcel
    @4
    @1
    vz
    cv
    #
    cid
    wbr
    #
    @6
    @2
    cA
    wbr
    #
    wa
    #
    vz
    wex
    #
    @5
    vz
    @1
    @2
    cA
    cid
    vx
    vex
    vy
    vex
    opelco
    @10
    @6
    @1
    wceq
    #
    @8
    wa
    #
    vz
    wex
    @5
    @9
    @12
    vz
    @7
    @11
    @8
    @7
    @1
    @6
    wceq
    @11
    @1
    @6
    vz
    vex
    ideq
    vx
    vz
    equcom
    bitri
    anbi1i
    exbii
    @8
    @5
    vz
    vx
    @6
    @1
    @2
    cA
    breq1
    equsexvw
    bitri
    bitri
    @1
    @2
    cA
    df-br
    bitri
    eqrelriv
    mpan
end
