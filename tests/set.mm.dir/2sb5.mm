include "wsb.mm"
include "weq.mm"
include "wa.mm"
include "wex.mm"
include "sb5.mm"
include "19.42v.mm"
include "anass.mm"
include "exbii.mm"
include "anbi2i.mm"
include "3bitr4ri.mm"
include "bitri.mm"

theorem 2sb5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint w y
  assert |- ( [ z / x ] [ w / y ] ph <-> E. x E. y ( ( x = z /\ y = w ) /\ ph ) )

  proof
    wph
    vy
    vw
    wsb
    #
    vx
    vz
    wsb
    vx
    vz
    weq
    #
    @0
    wa
    #
    vx
    wex
    @1
    vy
    vw
    weq
    #
    wa
    wph
    wa
    #
    vy
    wex
    #
    vx
    wex
    @0
    vx
    vz
    sb5
    @2
    @5
    vx
    @1
    @3
    wph
    wa
    #
    wa
    #
    vy
    wex
    @1
    @6
    vy
    wex
    #
    wa
    @5
    @2
    @1
    @6
    vy
    19.42v
    @4
    @7
    vy
    @1
    @3
    wph
    anass
    exbii
    @0
    @8
    @1
    wph
    vy
    vw
    sb5
    anbi2i
    3bitr4ri
    exbii
    bitri
end
