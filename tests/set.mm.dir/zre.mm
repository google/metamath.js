include "cz.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "wceq.mm"
include "cn.mm"
include "cneg.mm"
include "w3o.mm"
include "elz.mm"
include "simplbi.mm"

theorem zre
  let cN: class N


  assert |- ( N e. ZZ -> N e. RR )

  proof
    cN
    cz
    wcel
    cN
    cr
    wcel
    cN
    cc0
    wceq
    cN
    cn
    wcel
    cN
    cneg
    cn
    wcel
    w3o
    cN
    elz
    simplbi
end
