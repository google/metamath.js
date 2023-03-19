include "con0.mm"
include "wcel.mm"
include "c1o.mm"
include "coe.mm"
include "co.mm"
include "c0.mm"
include "comu.mm"
include "csuc.mm"
include "df-1o.mm"
include "oveq2i.mm"
include "com.mm"
include "wceq.mm"
include "peano1.mm"
include "onesuc.mm"
include "mpan2.mm"
include "syl5eq.mm"
include "oe0.mm"
include "oveq1d.mm"
include "om1r.mm"
include "3eqtrd.mm"

theorem oe1
  let cA: class A


  assert |- ( A e. On -> ( A ^o 1o ) = A )

  proof
    cA
    con0
    wcel
    #
    cA
    c1o
    coe
    co
    #
    cA
    c0
    coe
    co
    #
    cA
    comu
    co
    #
    c1o
    cA
    comu
    co
    cA
    @0
    @1
    cA
    c0
    csuc
    #
    coe
    co
    #
    @3
    c1o
    @4
    cA
    coe
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
    onesuc
    mpan2
    syl5eq
    @0
    @2
    c1o
    cA
    comu
    cA
    oe0
    oveq1d
    cA
    om1r
    3eqtrd
end
