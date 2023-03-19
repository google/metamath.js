include "cch.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "choccl.mm"
include "ax-mp.mm"

theorem choccli
  let cA: class A
  assume choccl.1: |- A e. CH


  assert |- ( _|_ ` A ) e. CH

  proof
    cA
    cch
    wcel
    cA
    cort
    cfv
    cch
    wcel
    choccl.1
    cA
    choccl
    ax-mp
end
