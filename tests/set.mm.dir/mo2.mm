include "wmo.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "mo2v.mm"
include "nfv.mm"
include "nfim.mm"
include "nfal.mm"
include "equequ2.mm"
include "imbi2d.mm"
include "albidv.mm"
include "cbvex.mm"
include "bitri.mm"

theorem mo2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume mo2.1: |- F/ y ph

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- ( E* x ph <-> E. y A. x ( ph -> x = y ) )

  proof
    wph
    vx
    wmo
    wph
    vx
    vz
    weq
    #
    wi
    #
    vx
    wal
    #
    vz
    wex
    wph
    vx
    vy
    weq
    #
    wi
    #
    vx
    wal
    #
    vy
    wex
    wph
    vx
    vz
    mo2v
    @2
    @5
    vz
    vy
    @1
    vy
    vx
    wph
    @0
    vy
    mo2.1
    @0
    vy
    nfv
    nfim
    nfal
    @5
    vz
    nfv
    vz
    vy
    weq
    #
    @1
    @4
    vx
    @6
    @0
    @3
    wph
    vz
    vy
    vx
    equequ2
    imbi2d
    albidv
    cbvex
    bitri
end
