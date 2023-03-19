include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "c2nd.mm"
include "cfv.mm"
include "wsbc.mm"
include "c1st.mm"
include "copab.mm"
include "crab.mm"
include "nfsbc1v.mm"
include "19.41.mm"
include "sbcopeq1a.mm"
include "pm5.32i.mm"
include "exbii.mm"
include "nfcv.mm"
include "nfsbc.mm"
include "bitr3i.mm"
include "elvv.mm"
include "anbi1i.mm"
include "3bitr4i.mm"
include "abbii.mm"
include "df-opab.mm"
include "df-rab.mm"
include "3eqtr4i.mm"

theorem dfopab2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint ph z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- { <. x , y >. | ph } = { z e. ( _V X. _V ) | [. ( 1st ` z ) / x ]. [. ( 2nd ` z ) / y ]. ph }

  proof
    vz
    cv
    #
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
    @0
    cvv
    cvv
    cxp
    #
    wcel
    #
    wph
    vy
    @0
    c2nd
    cfv
    #
    wsbc
    #
    vx
    @0
    c1st
    cfv
    #
    wsbc
    #
    wa
    #
    vz
    cab
    wph
    vx
    vy
    copab
    @10
    vz
    @5
    crab
    @4
    @11
    vz
    @1
    vy
    wex
    #
    @10
    wa
    #
    vx
    wex
    @12
    vx
    wex
    #
    @10
    wa
    @4
    @11
    @12
    @10
    vx
    @8
    vx
    @9
    nfsbc1v
    19.41
    @3
    @13
    vx
    @3
    @1
    @10
    wa
    #
    vy
    wex
    @13
    @15
    @2
    vy
    @1
    @10
    wph
    wph
    vx
    vy
    @0
    sbcopeq1a
    pm5.32i
    exbii
    @1
    @10
    vy
    @8
    vy
    vx
    @9
    vy
    @9
    nfcv
    wph
    vy
    @7
    nfsbc1v
    nfsbc
    19.41
    bitr3i
    exbii
    @6
    @14
    @10
    vx
    vy
    @0
    elvv
    anbi1i
    3bitr4i
    abbii
    wph
    vx
    vy
    vz
    df-opab
    @10
    vz
    @5
    df-rab
    3eqtr4i
end
