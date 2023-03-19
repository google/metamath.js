include "cc.mm"
include "casin.mm"
include "asinf.mm"
include "ffvelrni.mm"

theorem asincl
  let cA: class A


  assert |- ( A e. CC -> ( arcsin ` A ) e. CC )

  proof
    cc
    cc
    cA
    casin
    asinf
    ffvelrni
end
