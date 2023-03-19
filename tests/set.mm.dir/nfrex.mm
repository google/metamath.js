include "wrex.mm"
include "wnf.mm"
include "wtru.mm"
include "nftru.mm"
include "wnfc.mm"
include "a1i.mm"
include "nfrexd.mm"
include "trud.mm"

theorem nfrex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nfrex.1: |- F/_ x A
  assume nfrex.2: |- F/ x ph


  assert |- F/ x E. y e. A ph

  proof
    wph
    vy
    cA
    wrex
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
    nfrex.1
    a1i
    wph
    vx
    wnf
    wtru
    nfrex.2
    a1i
    nfrexd
    trud
end
