include "weu.mm"
include "wnf.mm"
include "wtru.mm"
include "nftru.mm"
include "a1i.mm"
include "nfeud.mm"
include "trud.mm"

theorem nfeu
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume nfeu.1: |- F/ x ph


  assert |- F/ x E! y ph

  proof
    wph
    vy
    weu
    vx
    wnf
    wtru
    wph
    vx
    vy
    vy
    nftru
    wph
    vx
    wnf
    wtru
    nfeu.1
    a1i
    nfeud
    trud
end
