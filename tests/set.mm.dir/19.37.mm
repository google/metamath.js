include "wi.mm"
include "wex.mm"
include "wal.mm"
include "19.35.mm"
include "19.3.mm"
include "imbi1i.mm"
include "bitri.mm"

theorem 19.37
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.37.1: |- F/ x ph


  assert |- ( E. x ( ph -> ps ) <-> ( ph -> E. x ps ) )

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
    wph
    @1
    wi
    wph
    wps
    vx
    19.35
    @0
    wph
    @1
    wph
    vx
    19.37.1
    19.3
    imbi1i
    bitri
end
