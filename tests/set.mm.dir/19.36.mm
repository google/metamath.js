include "wi.mm"
include "wex.mm"
include "wal.mm"
include "19.35.mm"
include "19.9.mm"
include "imbi2i.mm"
include "bitri.mm"

theorem 19.36
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  assume 19.36.1: |- F/ x ps


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
    19.36.1
    19.9
    imbi2i
    bitri
end
