include "wn.mm"
include "wnf.mm"
include "nfntht2.mm"
include "mpg.mm"

theorem nfnth
  let wph: wff ph
  let vx: setvar x
  assume nfnth.1: |- -. ph


  assert |- F/ x ph

  proof
    wph
    wn
    wph
    vx
    wnf
    vx
    wph
    vx
    nfntht2
    nfnth.1
    mpg
end
