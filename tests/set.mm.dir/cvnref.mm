include "cch.mm"
include "wcel.mm"
include "ccv.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "cvnsym.mm"
include "anidms.mm"
include "pm2.01d.mm"

theorem cvnref
  let cA: class A


  assert |- ( A e. CH -> -. A <oH A )

  proof
    cA
    cch
    wcel
    #
    cA
    cA
    ccv
    wbr
    #
    @0
    @1
    @1
    wn
    wi
    cA
    cA
    cvnsym
    anidms
    pm2.01d
end
