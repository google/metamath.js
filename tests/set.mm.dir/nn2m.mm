include "com.mm"
include "wcel.mm"
include "c2o.mm"
include "comu.mm"
include "co.mm"
include "coa.mm"
include "wceq.mm"
include "2onn.mm"
include "nnmcom.mm"
include "mpan.mm"
include "nnm2.mm"
include "eqtrd.mm"

theorem nn2m
  let cA: class A


  assert |- ( A e. _om -> ( 2o .o A ) = ( A +o A ) )

  proof
    cA
    com
    wcel
    #
    c2o
    cA
    comu
    co
    #
    cA
    c2o
    comu
    co
    #
    cA
    cA
    coa
    co
    c2o
    com
    wcel
    @0
    @1
    @2
    wceq
    2onn
    c2o
    cA
    nnmcom
    mpan
    cA
    nnm2
    eqtrd
end
