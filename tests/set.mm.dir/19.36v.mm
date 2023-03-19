include "wi.mm"
include "wex.mm"
include "wal.mm"
include "19.35.mm"
include "19.9v.mm"
include "imbi2i.mm"
include "bitri.mm"

theorem 19.36v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ps x
  assert |- ( E. x ( ph -> ps ) <-> ( A. x ph -> ps ) )

  proof
    wph
    wps
    wi
    vx
    wex
    wph
    vx
    wal
    #
    wps
    vx
    wex
    #
    wi
    @0
    wps
    wi
    wph
    wps
    vx
    19.35
    @1
    wps
    @0
    wps
    vx
    19.9v
    imbi2i
    bitri
end
