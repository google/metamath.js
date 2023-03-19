include "cc0.mm"
include "cprmo.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cprime.mm"
include "wcel.mm"
include "cif.mm"
include "cprod.mm"
include "c0.mm"
include "cn0.mm"
include "wceq.mm"
include "0nn0.mm"
include "prmoval.mm"
include "ax-mp.mm"
include "fz10.mm"
include "prodeq1i.mm"
include "prod0.mm"
include "3eqtri.mm"

theorem prmo0
  let vk: setvar k


  assert |- ( #p ` 0 ) = 1

  proof
    cc0
    cprmo
    cfv
    #
    c1
    cc0
    cfz
    co
    #
    vk
    cv
    #
    cprime
    wcel
    @2
    c1
    cif
    #
    vk
    cprod
    #
    c0
    @3
    vk
    cprod
    c1
    cc0
    cn0
    wcel
    @0
    @4
    wceq
    0nn0
    vk
    cc0
    prmoval
    ax-mp
    @1
    c0
    @3
    vk
    fz10
    prodeq1i
    @3
    vk
    prod0
    3eqtri
end
