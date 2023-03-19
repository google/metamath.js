include "wi.mm"
include "wex.mm"
include "wal.mm"
include "19.36v.mm"
include "exbii.mm"
include "bitri.mm"

theorem 19.36vv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint ps x
  disjoint ps y
  assert |- ( E. x E. y ( ph -> ps ) <-> ( A. x A. y ph -> ps ) )

  proof
    wph
    wps
    wi
    vy
    wex
    #
    vx
    wex
    wph
    vy
    wal
    #
    wps
    wi
    #
    vx
    wex
    @1
    vx
    wal
    wps
    wi
    @0
    @2
    vx
    wph
    wps
    vy
    19.36v
    exbii
    @1
    wps
    vx
    19.36v
    bitri
end
