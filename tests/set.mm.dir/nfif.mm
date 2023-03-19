include "cif.mm"
include "wnfc.mm"
include "wtru.mm"
include "wnf.mm"
include "a1i.mm"
include "nfifd.mm"
include "trud.mm"

theorem nfif
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nfif.1: |- F/ x ph
  assume nfif.2: |- F/_ x A
  assume nfif.3: |- F/_ x B


  assert |- F/_ x if ( ph , A , B )

  proof
    vx
    wph
    cA
    cB
    cif
    wnfc
    wtru
    wph
    vx
    cA
    cB
    wph
    vx
    wnf
    wtru
    nfif.1
    a1i
    vx
    cA
    wnfc
    wtru
    nfif.2
    a1i
    vx
    cB
    wnfc
    wtru
    nfif.3
    a1i
    nfifd
    trud
end
