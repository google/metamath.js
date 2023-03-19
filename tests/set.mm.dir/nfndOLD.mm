include "wnfOLD.mm"
include "wn.mm"
include "nfntOLD.mm"
include "syl.mm"

theorem nfndOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfndOLD.1: |- ( ph -> nfOLD x ps )


  assert |- ( ph -> nfOLD x -. ps )

  proof
    wph
    wps
    vx
    wnfOLD
    wps
    wn
    vx
    wnfOLD
    nfndOLD.1
    wps
    vx
    nfntOLD
    syl
end
