include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "cort.mm"
include "cfv.mm"
include "chsh.mm"
include "shoccl.mm"
include "syl.mm"

theorem choccl
  let cA: class A


  assert |- ( A e. CH -> ( _|_ ` A ) e. CH )

  proof
    cA
    cch
    wcel
    cA
    csh
    wcel
    cA
    cort
    cfv
    cch
    wcel
    cA
    chsh
    cA
    shoccl
    syl
end
