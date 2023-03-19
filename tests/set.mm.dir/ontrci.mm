include "word.mm"
include "wtr.mm"
include "onordi.mm"
include "ordtr.mm"
include "ax-mp.mm"

theorem ontrci
  let cA: class A
  assume on.1: |- A e. On


  assert |- Tr A

  proof
    cA
    word
    cA
    wtr
    cA
    on.1
    onordi
    cA
    ordtr
    ax-mp
end
