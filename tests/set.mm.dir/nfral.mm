include "wral.mm"
include "wnf.mm"
include "wtru.mm"
include "nftru.mm"
include "wnfc.mm"
include "a1i.mm"
include "nfrald.mm"
include "trud.mm"

theorem nfral
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nfral.1: |- F/_ x A
  assume nfral.2: |- F/ x ph


  assert |- F/ x A. y e. A ph

  proof
    wph
    vy
    cA
    wral
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
    nfral.1
    a1i
    wph
    vx
    wnf
    wtru
    nfral.2
    a1i
    nfrald
    trud
end
