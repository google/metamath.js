include "con0.mm"
include "wcel.mm"
include "c1o.mm"
include "coa.mm"
include "co.mm"
include "c0.mm"
include "csuc.mm"
include "df-1o.mm"
include "oveq2i.mm"
include "com.mm"
include "wceq.mm"
include "peano1.mm"
include "onasuc.mm"
include "mpan2.mm"
include "syl5eq.mm"
include "oa0.mm"
include "suceq.mm"
include "syl.mm"
include "eqtrd.mm"

theorem oa1suc
  let cA: class A


  assert |- ( A e. On -> ( A +o 1o ) = suc A )

  proof
    cA
    con0
    wcel
    #
    cA
    c1o
    coa
    co
    #
    cA
    c0
    coa
    co
    #
    csuc
    #
    cA
    csuc
    #
    @0
    @1
    cA
    c0
    csuc
    #
    coa
    co
    #
    @3
    c1o
    @5
    cA
    coa
    df-1o
    oveq2i
    @0
    c0
    com
    wcel
    @6
    @3
    wceq
    peano1
    cA
    c0
    onasuc
    mpan2
    syl5eq
    @0
    @2
    cA
    wceq
    @3
    @4
    wceq
    cA
    oa0
    @2
    cA
    suceq
    syl
    eqtrd
end
