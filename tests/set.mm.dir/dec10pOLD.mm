include "c1.mm"
include "cdc.mm"
include "c10.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "dfdecOLD.mm"
include "10nnOLD.mm"
include "nncni.mm"
include "mulid1i.mm"
include "oveq1i.mm"
include "eqtr2i.mm"

theorem dec10pOLD
  let cA: class A


  assert |- ( 10 + A ) = ; 1 A

  proof
    c1
    cA
    cdc
    c10
    c1
    cmul
    co
    #
    cA
    caddc
    co
    c10
    cA
    caddc
    co
    c1
    cA
    dfdecOLD
    @0
    c10
    cA
    caddc
    c10
    c10
    10nnOLD
    nncni
    mulid1i
    oveq1i
    eqtr2i
end
