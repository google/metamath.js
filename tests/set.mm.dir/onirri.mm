include "word.mm"
include "wcel.mm"
include "wn.mm"
include "onordi.mm"
include "ordirr.mm"
include "ax-mp.mm"

theorem onirri
  let cA: class A
  assume on.1: |- A e. On


  assert |- -. A e. A

  proof
    cA
    word
    cA
    cA
    wcel
    wn
    cA
    on.1
    onordi
    cA
    ordirr
    ax-mp
end
