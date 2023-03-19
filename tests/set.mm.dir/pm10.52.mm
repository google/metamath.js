include "wi.mm"
include "wal.mm"
include "wex.mm"
include "19.23v.mm"
include "pm5.5.mm"
include "syl5bb.mm"

theorem pm10.52
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ps x
  assert |- ( E. x ph -> ( A. x ( ph -> ps ) <-> ps ) )

  proof
    wph
    wps
    wi
    vx
    wal
    wph
    vx
    wex
    #
    wps
    wi
    @0
    wps
    wph
    wps
    vx
    19.23v
    @0
    wps
    pm5.5
    syl5bb
end
