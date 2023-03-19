include "wreu.mm"
include "wnf.mm"
include "wtru.mm"
include "nftru.mm"
include "wnfc.mm"
include "a1i.mm"
include "nfreud.mm"
include "trud.mm"

theorem nfreu
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nfreu.1: |- F/_ x A
  assume nfreu.2: |- F/ x ph


  assert |- F/ x E! y e. A ph

  proof
    wph
    vy
    cA
    wreu
    vx
    wnf
    wtru
    wph
    vx
    vy
    cA
    vy
    nftru
    vx
    cA
    wnfc
    wtru
    nfreu.1
    a1i
    wph
    vx
    wnf
    wtru
    nfreu.2
    a1i
    nfreud
    trud
end
