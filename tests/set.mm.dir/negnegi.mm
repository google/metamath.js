include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "wceq.mm"
include "negneg.mm"
include "ax-mp.mm"

theorem negnegi
  let cA: class A
  assume negidi.1: |- A e. CC


  assert |- -u -u A = A

  proof
    cA
    cc
    wcel
    cA
    cneg
    cneg
    cA
    wceq
    negidi.1
    cA
    negneg
    ax-mp
end
