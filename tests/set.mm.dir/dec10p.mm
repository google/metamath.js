include "c1.mm"
include "cdc.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "dfdec10.mm"
include "10nn.mm"
include "nncni.mm"
include "mulid1i.mm"
include "oveq1i.mm"
include "eqtr2i.mm"

theorem dec10p
  let cA: class A


  assert |- ( ; 1 0 + A ) = ; 1 A

  proof
    c1
    cA
    cdc
    c1
    cc0
    cdc
    #
    c1
    cmul
    co
    #
    cA
    caddc
    co
    @0
    cA
    caddc
    co
    c1
    cA
    dfdec10
    @1
    @0
    cA
    caddc
    @0
    @0
    10nn
    nncni
    mulid1i
    oveq1i
    eqtr2i
end
