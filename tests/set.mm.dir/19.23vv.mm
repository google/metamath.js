include "wi.mm"
include "wal.mm"
include "wex.mm"
include "19.23v.mm"
include "albii.mm"
include "bitri.mm"

theorem 19.23vv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint ps x
  disjoint ps y
  assert |- ( A. x A. y ( ph -> ps ) <-> ( E. x E. y ph -> ps ) )

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
    vy
    wex
    #
    wps
    wi
    #
    vx
    wal
    @1
    vx
    wex
    wps
    wi
    @0
    @2
    vx
    wph
    wps
    vy
    19.23v
    albii
    @1
    wps
    vx
    19.23v
    bitri
end
