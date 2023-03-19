include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "1z.mm"
include "zaddcl.mm"
include "mpan2.mm"

theorem peano2z
  let cN: class N


  assert |- ( N e. ZZ -> ( N + 1 ) e. ZZ )

  proof
    cN
    cz
    wcel
    c1
    cz
    wcel
    cN
    c1
    caddc
    co
    cz
    wcel
    1z
    cN
    c1
    zaddcl
    mpan2
end
