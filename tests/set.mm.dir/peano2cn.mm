include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "ax-1cn.mm"
include "addcl.mm"
include "mpan2.mm"

theorem peano2cn
  let cA: class A


  assert |- ( A e. CC -> ( A + 1 ) e. CC )

  proof
    cA
    cc
    wcel
    c1
    cc
    wcel
    cA
    c1
    caddc
    co
    cc
    wcel
    ax-1cn
    cA
    c1
    addcl
    mpan2
end
