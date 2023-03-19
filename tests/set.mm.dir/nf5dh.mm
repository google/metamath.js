include "wal.mm"
include "wi.mm"
include "wnf.mm"
include "alrimih.mm"
include "nf5-1.mm"
include "syl.mm"

theorem nf5dh
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nf5dh.1: |- ( ph -> A. x ph )
  assume nf5dh.2: |- ( ph -> ( ps -> A. x ps ) )


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
    nf5dh.1
    nf5dh.2
    alrimih
    wps
    vx
    nf5-1
    syl
end
