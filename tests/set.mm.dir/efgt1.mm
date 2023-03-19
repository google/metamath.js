include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "1red.mm"
include "cr.mm"
include "1re.mm"
include "rpre.mm"
include "readdcl.mm"
include "sylancr.mm"
include "reefcld.mm"
include "clt.mm"
include "wbr.mm"
include "ltaddrp.mm"
include "mpan.mm"
include "efgt1p.mm"
include "lttrd.mm"

theorem efgt1
  let cA: class A
  let vn: setvar n


  assert |- ( A e. RR+ -> 1 < ( exp ` A ) )

  proof
    cA
    crp
    wcel
    #
    c1
    c1
    cA
    caddc
    co
    #
    cA
    ce
    cfv
    @0
    1red
    @0
    c1
    cr
    wcel
    #
    cA
    cr
    wcel
    @1
    cr
    wcel
    1re
    cA
    rpre
    #
    c1
    cA
    readdcl
    sylancr
    @0
    cA
    @3
    reefcld
    @2
    @0
    c1
    @1
    clt
    wbr
    1re
    c1
    cA
    ltaddrp
    mpan
    cA
    efgt1p
    lttrd
end
