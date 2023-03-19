include "c3.mm"
include "cfz.mm"
include "co.mm"
include "cc0.mm"
include "cr.mm"
include "0re.mm"
include "fconst6.mm"

theorem axlowdimlem1
  let cN: class N


  assert |- ( ( 3 ... N ) X. { 0 } ) : ( 3 ... N ) --> RR

  proof
    c3
    cN
    cfz
    co
    cc0
    cr
    0re
    fconst6
end
