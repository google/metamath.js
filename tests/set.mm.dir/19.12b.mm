include "wi.mm"
include "wal.mm"
include "wex.mm"
include "19.21.mm"
include "exbii.mm"
include "nfal.mm"
include "19.36.mm"
include "albii.mm"
include "bitr2i.mm"
include "3bitri.mm"

theorem 19.12b
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume 19.12b.1: |- F/ y ph
  assume 19.12b.2: |- F/ x ps

  disjoint x y
  assert |- ( E. x A. y ( ph -> ps ) <-> A. y E. x ( ph -> ps ) )

  proof
    wph
    wps
    wi
    #
    vy
    wal
    #
    vx
    wex
    wph
    wps
    vy
    wal
    #
    wi
    #
    vx
    wex
    wph
    vx
    wal
    #
    @2
    wi
    #
    @0
    vx
    wex
    #
    vy
    wal
    #
    @1
    @3
    vx
    wph
    wps
    vy
    19.12b.1
    19.21
    exbii
    wph
    @2
    vx
    wps
    vx
    vy
    19.12b.2
    nfal
    19.36
    @7
    @4
    wps
    wi
    #
    vy
    wal
    @5
    @6
    @8
    vy
    wph
    wps
    vx
    19.12b.2
    19.36
    albii
    @4
    wps
    vy
    wph
    vy
    vx
    19.12b.1
    nfal
    19.21
    bitr2i
    3bitri
end
