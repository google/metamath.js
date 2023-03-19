include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "sqcl.mm"
include "ax-mp.mm"

theorem sqcli
  let cA: class A
  assume sqval.1: |- A e. CC


  assert |- ( A ^ 2 ) e. CC

  proof
    cA
    cc
    wcel
    cA
    c2
    cexp
    co
    cc
    wcel
    sqval.1
    cA
    sqcl
    ax-mp
end
