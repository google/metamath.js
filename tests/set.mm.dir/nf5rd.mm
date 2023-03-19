include "wnf.mm"
include "wal.mm"
include "wi.mm"
include "nf5r.mm"
include "syl.mm"

theorem nf5rd
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  assume nf5rd.1: |- ( ph -> F/ x ps )


  assert |- ( ph -> ( ps -> A. x ps ) )

  proof
    wph
    wps
    vx
    wnf
    wps
    wps
    vx
    wal
    wi
    nf5rd.1
    wps
    vx
    nf5r
    syl
end
