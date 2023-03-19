include "cneg.mm"
include "wnfc.mm"
include "wtru.mm"
include "a1i.mm"
include "nfnegd.mm"
include "trud.mm"

theorem nfneg
  let vx: setvar x
  let cA: class A
  assume nfneg.1: |- F/_ x A


  assert |- F/_ x -u A

  proof
    vx
    cA
    cneg
    wnfc
    wtru
    vx
    cA
    vx
    cA
    wnfc
    wtru
    nfneg.1
    a1i
    nfnegd
    trud
end
