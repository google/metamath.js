include "wb.mm"
include "wnfOLD.mm"
include "wtru.mm"
include "a1i.mm"
include "nfbidOLD.mm"
include "trud.mm"

theorem nfbiOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfOLD.1: |- nfOLD x ph
  assume nfOLD.2: |- nfOLD x ps


  assert |- nfOLD x ( ph <-> ps )

  proof
    wph
    wps
    wb
    vx
    wnfOLD
    wtru
    wph
    wps
    vx
    wph
    vx
    wnfOLD
    wtru
    nfOLD.1
    a1i
    wps
    vx
    wnfOLD
    wtru
    nfOLD.2
    a1i
    nfbidOLD
    trud
end
