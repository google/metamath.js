include "wnfOLD.mm"
include "wn.mm"
include "nfntOLD.mm"
include "ax-mp.mm"

theorem nfnOLD
  let wph: wff ph
  let vx: setvar x
  assume nfnOLD.1: |- nfOLD x ph


  assert |- nfOLD x -. ph

  proof
    wph
    vx
    wnfOLD
    wph
    wn
    vx
    wnfOLD
    nfnOLD.1
    wph
    vx
    nfntOLD
    ax-mp
end
