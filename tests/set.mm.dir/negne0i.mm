include "cc0.mm"
include "wne.mm"
include "cneg.mm"
include "negne0bi.mm"
include "mpbi.mm"

theorem negne0i
  let cA: class A
  assume negidi.1: |- A e. CC
  assume negne0i.2: |- A =/= 0


  assert |- -u A =/= 0

  proof
    cA
    cc0
    wne
    cA
    cneg
    cc0
    wne
    negne0i.2
    cA
    negidi.1
    negne0bi
    mpbi
end
