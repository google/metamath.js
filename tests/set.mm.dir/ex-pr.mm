include "c1.mm"
include "cneg.mm"
include "cpr.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "elpri.mm"
include "oveq1.mm"
include "sq1.mm"
include "syl6eq.mm"
include "neg1sqe1.mm"
include "jaoi.mm"
include "syl.mm"

theorem ex-pr
  let cA: class A


  assert |- ( A e. { 1 , -u 1 } -> ( A ^ 2 ) = 1 )

  proof
    cA
    c1
    c1
    cneg
    #
    cpr
    wcel
    cA
    c1
    wceq
    #
    cA
    @0
    wceq
    #
    wo
    cA
    c2
    cexp
    co
    #
    c1
    wceq
    #
    cA
    c1
    @0
    elpri
    @1
    @4
    @2
    @1
    @3
    c1
    c2
    cexp
    co
    c1
    cA
    c1
    c2
    cexp
    oveq1
    sq1
    syl6eq
    @2
    @3
    @0
    c2
    cexp
    co
    c1
    cA
    @0
    c2
    cexp
    oveq1
    neg1sqe1
    syl6eq
    jaoi
    syl
end
