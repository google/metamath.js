include "wmo.mm"
include "wnf.mm"
include "wtru.mm"
include "nftru.mm"
include "a1i.mm"
include "nfmod.mm"
include "trud.mm"

theorem nfmo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume nfeu.1: |- F/ x ph


  assert |- F/ x E* y ph

  proof
    wph
    vy
    wmo
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
    nfmod
    trud
end
