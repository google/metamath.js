include "wex.mm"
include "wal.mm"
include "wi.mm"
include "wnf.mm"
include "df-nf.mm"
include "sylibr.mm"

theorem nfd
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  assume nfd.1: |- ( ph -> ( E. x ps -> A. x ps ) )


  assert |- ( ph -> F/ x ps )

  proof
    wph
    wps
    vx
    wex
    wps
    vx
    wal
    wi
    wps
    vx
    wnf
    nfd.1
    wps
    vx
    df-nf
    sylibr
end
