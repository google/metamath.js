include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "1z.mm"
include "zsubcl.mm"
include "mpan2.mm"

theorem peano2zm
  let cN: class N


  assert |- ( N e. ZZ -> ( N - 1 ) e. ZZ )

  proof
    cN
    cz
    wcel
    c1
    cz
    wcel
    cN
    c1
    cmin
    co
    cz
    wcel
    1z
    cN
    c1
    zsubcl
    mpan2
end
