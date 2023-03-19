include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "wa.mm"
include "comu.mm"
include "co.mm"
include "wceq.mm"
include "om0.mm"
include "adantr.mm"
include "cxp.mm"
include "wfn.mm"
include "cdm.mm"
include "fnom.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "pm2.61i.mm"

theorem om0x
  let cA: class A


  assert |- ( A .o (/) ) = (/)

  proof
    cA
    con0
    wcel
    #
    c0
    con0
    wcel
    #
    wa
    cA
    c0
    comu
    co
    c0
    wceq
    #
    @0
    @2
    @1
    cA
    om0
    adantr
    cA
    c0
    con0
    comu
    comu
    con0
    con0
    cxp
    #
    wfn
    comu
    cdm
    @3
    wceq
    fnom
    @3
    comu
    fndm
    ax-mp
    ndmov
    pm2.61i
end
