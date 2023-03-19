include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cc0.mm"
include "caddc.mm"
include "1e0p1.mm"
include "oveq1i.mm"
include "cz.mm"
include "wcel.mm"
include "wss.mm"
include "0z.mm"
include "fzp1ss.mm"
include "ax-mp.mm"
include "eqsstri.mm"

theorem fz1ssfz0
  let cN: class N


  assert |- ( 1 ... N ) C_ ( 0 ... N )

  proof
    c1
    cN
    cfz
    co
    cc0
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    cc0
    cN
    cfz
    co
    #
    c1
    @0
    cN
    cfz
    1e0p1
    oveq1i
    cc0
    cz
    wcel
    @1
    @2
    wss
    0z
    cc0
    cN
    fzp1ss
    ax-mp
    eqsstri
end
