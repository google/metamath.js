include "cv.mm"
include "wceq.mm"
include "copab.mm"
include "cid.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "ccoss.mm"
include "equvinv.mm"
include "wb.mm"
include "cvv.mm"
include "ideqg.mm"
include "elv.mm"
include "anbi12i.mm"
include "exbii.mm"
include "bitr4i.mm"
include "opabbii.mm"
include "dfid3.mm"
include "df-coss.mm"
include "3eqtr4ri.mm"

theorem cossid
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ,~ _I = _I

  proof
    vy
    cv
    #
    vz
    cv
    #
    wceq
    #
    vy
    vz
    copab
    vx
    cv
    #
    @0
    cid
    wbr
    #
    @3
    @1
    cid
    wbr
    #
    wa
    #
    vx
    wex
    #
    vy
    vz
    copab
    cid
    cid
    ccoss
    @2
    @7
    vy
    vz
    @2
    @3
    @0
    wceq
    #
    @3
    @1
    wceq
    #
    wa
    #
    vx
    wex
    @7
    vy
    vz
    vx
    equvinv
    @6
    @10
    vx
    @4
    @8
    @5
    @9
    @4
    @8
    wb
    vy
    @3
    @0
    cvv
    ideqg
    elv
    @5
    @9
    wb
    vz
    @3
    @1
    cvv
    ideqg
    elv
    anbi12i
    exbii
    bitr4i
    opabbii
    vy
    vz
    dfid3
    vy
    vz
    vx
    cid
    df-coss
    3eqtr4ri
end
