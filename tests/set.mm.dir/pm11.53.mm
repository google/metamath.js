include "wi.mm"
include "wal.mm"
include "wex.mm"
include "19.21v.mm"
include "albii.mm"
include "nfv.mm"
include "nfal.mm"
include "19.23.mm"
include "bitri.mm"

theorem pm11.53
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint ph y
  disjoint ps x
  assert |- ( A. x A. y ( ph -> ps ) <-> ( E. x ph -> A. y ps ) )

  proof
    wph
    wps
    wi
    vy
    wal
    #
    vx
    wal
    wph
    wps
    vy
    wal
    #
    wi
    #
    vx
    wal
    wph
    vx
    wex
    @1
    wi
    @0
    @2
    vx
    wph
    wps
    vy
    19.21v
    albii
    wph
    @1
    vx
    wps
    vx
    vy
    wps
    vx
    nfv
    nfal
    19.23
    bitri
end
