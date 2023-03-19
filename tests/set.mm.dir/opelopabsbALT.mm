include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "wcel.mm"
include "wsb.mm"
include "excom.mm"
include "vex.mm"
include "opth.mm"
include "equcom.mm"
include "anbi12ci.mm"
include "bitri.mm"
include "anbi1i.mm"
include "2exbii.mm"
include "elopab.mm"
include "2sb5.mm"
include "3bitr4i.mm"

theorem opelopabsbALT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint w x
  disjoint w y
  assert |- ( <. z , w >. e. { <. x , y >. | ph } <-> [ w / y ] [ z / x ] ph )

  proof
    vz
    cv
    #
    vw
    cv
    #
    cop
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
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
    @4
    @1
    wceq
    #
    @3
    @0
    wceq
    #
    wa
    #
    wph
    wa
    #
    vx
    wex
    vy
    wex
    #
    @2
    wph
    vx
    vy
    copab
    wcel
    wph
    vx
    vz
    wsb
    vy
    vw
    wsb
    @7
    @6
    vx
    wex
    vy
    wex
    @12
    @6
    vx
    vy
    excom
    @6
    @11
    vy
    vx
    @5
    @10
    wph
    @5
    @0
    @3
    wceq
    #
    @1
    @4
    wceq
    #
    wa
    @10
    @0
    @1
    @3
    @4
    vz
    vex
    vw
    vex
    opth
    @13
    @9
    @14
    @8
    vz
    vx
    equcom
    vw
    vy
    equcom
    anbi12ci
    bitri
    anbi1i
    2exbii
    bitri
    wph
    vx
    vy
    @2
    elopab
    wph
    vy
    vx
    vw
    vz
    2sb5
    3bitr4i
end
