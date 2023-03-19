include "crio.mm"
include "wnfc.mm"
include "wtru.mm"
include "nftru.mm"
include "wnf.mm"
include "a1i.mm"
include "nfriotad.mm"
include "trud.mm"

theorem nfriota
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nfriota.1: |- F/ x ph
  assume nfriota.2: |- F/_ x A

  disjoint x y
  assert |- F/_ x ( iota_ y e. A ph )

  proof
    vx
    wph
    vy
    cA
    crio
    wnfc
    wtru
    wph
    vx
    vy
    cA
    vy
    nftru
    wph
    vx
    wnf
    wtru
    nfriota.1
    a1i
    vx
    cA
    wnfc
    wtru
    nfriota.2
    a1i
    nfriotad
    trud
end
