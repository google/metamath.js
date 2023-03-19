include "wnf.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wb.mm"
include "19.23t.mm"
include "ax-mp.mm"

theorem 19.23
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  assume 19.23.1: |- F/ x ps


  assert |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) )

  proof
    wps
    vx
    wnf
    wph
    wps
    wi
    vx
    wal
    wph
    vx
    wex
    wps
    wi
    wb
    19.23.1
    wph
    wps
    vx
    19.23t
    ax-mp
end
