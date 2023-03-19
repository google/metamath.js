include "wnf.mm"
include "nfbii.mm"
include "mpbir.mm"

theorem nfxfr
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfbii.1: |- ( ph <-> ps )
  assume nfxfr.2: |- F/ x ps


  assert |- F/ x ph

  proof
    wph
    vx
    wnf
    wps
    vx
    wnf
    nfxfr.2
    wph
    wps
    vx
    nfbii.1
    nfbii
    mpbir
end
