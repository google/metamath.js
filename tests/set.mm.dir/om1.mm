include "con0.mm"
include "wcel.mm"
include "c1o.mm"
include "comu.mm"
include "co.mm"
include "c0.mm"
include "coa.mm"
include "csuc.mm"
include "df-1o.mm"
include "oveq2i.mm"
include "com.mm"
include "wceq.mm"
include "peano1.mm"
include "onmsuc.mm"
include "mpan2.mm"
include "syl5eq.mm"
include "om0.mm"
include "oveq1d.mm"
include "oa0r.mm"
include "3eqtrd.mm"

theorem om1
  let cA: class A


  assert |- ( A e. On -> ( A .o 1o ) = A )

  proof
    cA
    con0
    wcel
    #
    cA
    c1o
    comu
    co
    #
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
    @1
    cA
    c0
    csuc
    #
    comu
    co
    #
    @3
    c1o
    @4
    cA
    comu
    df-1o
    oveq2i
    @0
    c0
    com
    wcel
    @5
    @3
    wceq
    peano1
    cA
    c0
    onmsuc
    mpan2
    syl5eq
    @0
    @2
    c0
    cA
    coa
    cA
    om0
    oveq1d
    cA
    oa0r
    3eqtrd
end
