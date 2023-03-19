include "cio.mm"
include "wnfc.mm"
include "wtru.mm"
include "nftru.mm"
include "wnf.mm"
include "a1i.mm"
include "nfiotad.mm"
include "trud.mm"

theorem nfiota
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume nfiota.1: |- F/ x ph


  assert |- F/_ x ( iota y ph )

  proof
    vx
    wph
    vy
    cio
    wnfc
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
    nfiota.1
    a1i
    nfiotad
    trud
end
