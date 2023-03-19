include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "1re.mm"
include "readdcl.mm"
include "mpan2.mm"

theorem peano2re
  let cA: class A


  assert |- ( A e. RR -> ( A + 1 ) e. RR )

  proof
    cA
    cr
    wcel
    c1
    cr
    wcel
    cA
    c1
    caddc
    co
    cr
    wcel
    1re
    cA
    c1
    readdcl
    mpan2
end
