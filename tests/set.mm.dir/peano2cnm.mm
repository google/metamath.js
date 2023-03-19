include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "mpan2.mm"

theorem peano2cnm
  let cN: class N


  assert |- ( N e. CC -> ( N - 1 ) e. CC )

  proof
    cN
    cc
    wcel
    c1
    cc
    wcel
    cN
    c1
    cmin
    co
    cc
    wcel
    ax-1cn
    cN
    c1
    subcl
    mpan2
end
