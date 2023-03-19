include "com.mm"
include "wcel.mm"
include "c2o.mm"
include "comu.mm"
include "co.mm"
include "c1o.mm"
include "csuc.mm"
include "coa.mm"
include "df-2o.mm"
include "oveq2i.mm"
include "wceq.mm"
include "1onn.mm"
include "nnmsuc.mm"
include "mpan2.mm"
include "nnm1.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem nnm2
  let cA: class A


  assert |- ( A e. _om -> ( A .o 2o ) = ( A +o A ) )

  proof
    cA
    com
    wcel
    #
    cA
    c2o
    comu
    co
    cA
    c1o
    csuc
    #
    comu
    co
    #
    cA
    cA
    coa
    co
    #
    c2o
    @1
    cA
    comu
    df-2o
    oveq2i
    @0
    @2
    cA
    c1o
    comu
    co
    #
    cA
    coa
    co
    #
    @3
    @0
    c1o
    com
    wcel
    @2
    @5
    wceq
    1onn
    cA
    c1o
    nnmsuc
    mpan2
    @0
    @4
    cA
    cA
    coa
    cA
    nnm1
    oveq1d
    eqtrd
    syl5eq
end
