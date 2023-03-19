include "wnf.mm"
include "nftht.mm"
include "mpg.mm"

theorem nfth
  let wph: wff ph
  let vx: setvar x
  assume nfth.1: |- ph


  assert |- F/ x ph

  proof
    wph
    wph
    vx
    wnf
    vx
    wph
    vx
    nftht
    nfth.1
    mpg
end
