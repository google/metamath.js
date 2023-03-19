include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "coprab.mm"
include "copab.mm"
include "excom.mm"
include "exrot4.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "pm5.32ri.mm"
include "anbi1i.mm"
include "anass.mm"
include "an32.mm"
include "3bitr3i.mm"
include "exbii.mm"
include "opex.mm"
include "isseti.mm"
include "19.42v.mm"
include "mpbiran2.mm"
include "bitri.mm"
include "3exbii.mm"
include "19.42vv.mm"
include "2exbii.mm"
include "abbii.mm"
include "df-oprab.mm"
include "df-opab.mm"
include "3eqtr4i.mm"

theorem dfoprab2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v

  disjoint x z
  disjoint w x
  disjoint w z
  disjoint y z
  disjoint w y
  disjoint ph w
  disjoint v x
  disjoint v z
  disjoint v w
  disjoint v y
  disjoint ph v
  assert |- { <. <. x , y >. , z >. | ph } = { <. w , z >. | E. x E. y ( w = <. x , y >. /\ ph ) }

  proof
    vv
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
    wph
    wa
    #
    vz
    wex
    vy
    wex
    vx
    wex
    #
    vv
    cab
    @0
    vw
    cv
    #
    @4
    cop
    #
    wceq
    #
    @9
    @3
    wceq
    #
    wph
    wa
    #
    vy
    wex
    vx
    wex
    #
    wa
    #
    vz
    wex
    vw
    wex
    #
    vv
    cab
    wph
    vx
    vy
    vz
    coprab
    @14
    vw
    vz
    copab
    @8
    @16
    vv
    @11
    @13
    wa
    #
    vy
    wex
    vx
    wex
    #
    vw
    wex
    vz
    wex
    #
    @18
    vz
    wex
    vw
    wex
    @8
    @16
    @18
    vz
    vw
    excom
    @19
    @17
    vw
    wex
    #
    vz
    wex
    vy
    wex
    vx
    wex
    @8
    @17
    vz
    vw
    vx
    vy
    exrot4
    @20
    @7
    vx
    vy
    vz
    @20
    @7
    @12
    wa
    #
    vw
    wex
    #
    @7
    @17
    @21
    vw
    @11
    @12
    wa
    #
    wph
    wa
    @6
    @12
    wa
    #
    wph
    wa
    @17
    @21
    @23
    @24
    wph
    @12
    @11
    @6
    @12
    @10
    @5
    @0
    @9
    @3
    @4
    opeq1
    eqeq2d
    pm5.32ri
    anbi1i
    @11
    @12
    wph
    anass
    @6
    @12
    wph
    an32
    3bitr3i
    exbii
    @22
    @7
    @12
    vw
    wex
    vw
    @3
    @1
    @2
    opex
    isseti
    @7
    @12
    vw
    19.42v
    mpbiran2
    bitri
    3exbii
    bitri
    @18
    @15
    vw
    vz
    @11
    @13
    vx
    vy
    19.42vv
    2exbii
    3bitr3i
    abbii
    wph
    vx
    vy
    vz
    vv
    df-oprab
    @14
    vw
    vz
    vv
    df-opab
    3eqtr4i
end
