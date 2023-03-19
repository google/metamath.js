include "wnfOLD.mm"
include "wal.mm"
include "wi.mm"
include "nfrOLD.mm"
include "syl.mm"

theorem nfrdOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfrdOLD.1: |- ( ph -> nfOLD x ps )


  assert |- ( ph -> ( ps -> A. x ps ) )

  proof
    wph
    wps
    vx
    wnfOLD
    wps
    wps
    vx
    wal
    wi
    nfrdOLD.1
    wps
    vx
    nfrOLD
    syl
end
