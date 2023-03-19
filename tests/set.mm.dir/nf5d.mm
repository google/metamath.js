include "wal.mm"
include "wi.mm"
include "wnf.mm"
include "alrimi.mm"
include "nf5-1.mm"
include "syl.mm"

theorem nf5d
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  assume nf5d.1: |- F/ x ph
  assume nf5d.2: |- ( ph -> ( ps -> A. x ps ) )


  assert |- ( ph -> F/ x ps )

  proof
    wph
    wps
    wps
    vx
    wal
    wi
    #
    vx
    wal
    wps
    vx
    wnf
    wph
    @0
    vx
    nf5d.1
    nf5d.2
    alrimi
    wps
    vx
    nf5-1
    syl
end
