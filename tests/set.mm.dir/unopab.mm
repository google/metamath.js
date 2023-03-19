include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cun.mm"
include "wo.mm"
include "copab.mm"
include "unab.mm"
include "19.43.mm"
include "andi.mm"
include "exbii.mm"
include "bitr2i.mm"
include "bitr3i.mm"
include "abbii.mm"
include "eqtri.mm"
include "df-opab.mm"
include "uneq12i.mm"
include "3eqtr4i.mm"

theorem unopab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( { <. x , y >. | ph } u. { <. x , y >. | ps } ) = { <. x , y >. | ( ph \/ ps ) }

  proof
    vz
    cv
    vx
    cv
    vy
    cv
    cop
    wceq
    #
    wph
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    vz
    cab
    #
    @0
    wps
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    vz
    cab
    #
    cun
    #
    @0
    wph
    wps
    wo
    #
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    vz
    cab
    #
    wph
    vx
    vy
    copab
    #
    wps
    vx
    vy
    copab
    #
    cun
    @10
    vx
    vy
    copab
    @9
    @3
    @7
    wo
    #
    vz
    cab
    @14
    @3
    @7
    vz
    unab
    @17
    @13
    vz
    @17
    @2
    @6
    wo
    #
    vx
    wex
    @13
    @2
    @6
    vx
    19.43
    @18
    @12
    vx
    @12
    @1
    @5
    wo
    #
    vy
    wex
    @18
    @11
    @19
    vy
    @0
    wph
    wps
    andi
    exbii
    @1
    @5
    vy
    19.43
    bitr2i
    exbii
    bitr3i
    abbii
    eqtri
    @15
    @4
    @16
    @8
    wph
    vx
    vy
    vz
    df-opab
    wps
    vx
    vy
    vz
    df-opab
    uneq12i
    @10
    vx
    vy
    vz
    df-opab
    3eqtr4i
end
