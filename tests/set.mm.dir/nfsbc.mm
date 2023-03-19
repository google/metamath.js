include "wsbc.mm"
include "wnf.mm"
include "wtru.mm"
include "nftru.mm"
include "wnfc.mm"
include "a1i.mm"
include "nfsbcd.mm"
include "trud.mm"

theorem nfsbc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nfsbc.1: |- F/_ x A
  assume nfsbc.2: |- F/ x ph


  assert |- F/ x [. A / y ]. ph

  proof
    wph
    vy
    cA
    wsbc
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
    nfsbc.1
    a1i
    wph
    vx
    wnf
    wtru
    nfsbc.2
    a1i
    nfsbcd
    trud
end
