include "wex.mm"
include "wsb.mm"
include "nfv.mm"
include "sb8e.mm"
include "exbii.mm"
include "excom.mm"
include "bitri.mm"
include "nfsb.mm"
include "3bitri.mm"

theorem 2sb8e
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint w z
  disjoint ph z
  disjoint ph w
  assert |- ( E. x E. y ph <-> E. z E. w [ z / x ] [ w / y ] ph )

  proof
    wph
    vy
    wex
    #
    vx
    wex
    #
    wph
    vy
    vw
    wsb
    #
    vx
    wex
    #
    vw
    wex
    #
    @2
    vx
    vz
    wsb
    #
    vz
    wex
    #
    vw
    wex
    @5
    vw
    wex
    vz
    wex
    @1
    @2
    vw
    wex
    #
    vx
    wex
    @4
    @0
    @7
    vx
    wph
    vy
    vw
    wph
    vw
    nfv
    sb8e
    exbii
    @2
    vx
    vw
    excom
    bitri
    @3
    @6
    vw
    @2
    vx
    vz
    wph
    vy
    vw
    vz
    wph
    vz
    nfv
    nfsb
    sb8e
    exbii
    @5
    vw
    vz
    excom
    3bitri
end
