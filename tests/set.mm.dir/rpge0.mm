include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "rpre.mm"
include "rpgt0.mm"
include "wi.mm"
include "0re.mm"
include "ltle.mm"
include "mpan.mm"
include "sylc.mm"

theorem rpge0
  let cA: class A


  assert |- ( A e. RR+ -> 0 <_ A )

  proof
    cA
    crp
    wcel
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    rpre
    cA
    rpgt0
    cc0
    cr
    wcel
    @0
    @1
    @2
    wi
    0re
    cc0
    cA
    ltle
    mpan
    sylc
end
