include "wnfOLD.mm"
include "nfbiiOLD.mm"
include "sylibr.mm"

theorem nfxfrdOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume nfbiiOLD.1: |- ( ph <-> ps )
  assume nfxfrdOLD.2: |- ( ch -> nfOLD x ps )


  assert |- ( ch -> nfOLD x ph )

  proof
    wch
    wps
    vx
    wnfOLD
    wph
    vx
    wnfOLD
    nfxfrdOLD.2
    wph
    wps
    vx
    nfbiiOLD.1
    nfbiiOLD
    sylibr
end
