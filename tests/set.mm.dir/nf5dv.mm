include "wal.mm"
include "wi.mm"
include "wnf.mm"
include "alrimiv.mm"
include "nf5-1.mm"
include "syl.mm"

theorem nf5dv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nf5dv.1: |- ( ph -> ( ps -> A. x ps ) )

  disjoint ph x
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
    nf5dv.1
    alrimiv
    wps
    vx
    nf5-1
    syl
end
