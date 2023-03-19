include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "cch.mm"
include "shss.mm"
include "occl.mm"
include "syl.mm"

theorem shoccl
  let cA: class A


  assert |- ( A e. SH -> ( _|_ ` A ) e. CH )

  proof
    cA
    csh
    wcel
    cA
    chil
    wss
    cA
    cort
    cfv
    cch
    wcel
    cA
    shss
    cA
    occl
    syl
end
