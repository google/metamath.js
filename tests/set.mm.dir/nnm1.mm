include "com.mm"
include "wcel.mm"
include "c1o.mm"
include "comu.mm"
include "co.mm"
include "c0.mm"
include "csuc.mm"
include "df-1o.mm"
include "oveq2i.mm"
include "coa.mm"
include "wceq.mm"
include "peano1.mm"
include "nnmsuc.mm"
include "mpan2.mm"
include "nnm0.mm"
include "oveq1d.mm"
include "nna0r.mm"
include "3eqtrd.mm"
include "syl5eq.mm"

theorem nnm1
  let cA: class A


  assert |- ( A e. _om -> ( A .o 1o ) = A )

  proof
    cA
    com
    wcel
    #
    cA
    c1o
    comu
    co
    cA
    c0
    csuc
    #
    comu
    co
    #
    cA
    c1o
    @1
    cA
    comu
    df-1o
    oveq2i
    @0
    @2
    cA
    c0
    comu
    co
    #
    cA
    coa
    co
    #
    c0
    cA
    coa
    co
    cA
    @0
    c0
    com
    wcel
    @2
    @4
    wceq
    peano1
    cA
    c0
    nnmsuc
    mpan2
    @0
    @3
    c0
    cA
    coa
    cA
    nnm0
    oveq1d
    cA
    nna0r
    3eqtrd
    syl5eq
end
