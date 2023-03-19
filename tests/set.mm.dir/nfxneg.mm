include "cxne.mm"
include "wnfc.mm"
include "wtru.mm"
include "a1i.mm"
include "nfxnegd.mm"
include "trud.mm"

theorem nfxneg
  let vx: setvar x
  let cA: class A
  assume nfxneg.1: |- F/_ x A


  assert |- F/_ x -e A

  proof
    vx
    cA
    cxne
    wnfc
    wtru
    vx
    cA
    vx
    cA
    wnfc
    wtru
    nfxneg.1
    a1i
    nfxnegd
    trud
end
