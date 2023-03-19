include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "1re.mm"
include "resubcl.mm"
include "mpan2.mm"

theorem peano2rem
  let cN: class N


  assert |- ( N e. RR -> ( N - 1 ) e. RR )

  proof
    cN
    cr
    wcel
    c1
    cr
    wcel
    cN
    c1
    cmin
    co
    cr
    wcel
    1re
    cN
    c1
    resubcl
    mpan2
end
