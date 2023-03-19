include "cc0.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "oveq1.mm"
include "sq0.mm"
include "syl6eq.mm"

theorem sq0i
  let cA: class A


  assert |- ( A = 0 -> ( A ^ 2 ) = 0 )

  proof
    cA
    cc0
    wceq
    cA
    c2
    cexp
    co
    cc0
    c2
    cexp
    co
    cc0
    cA
    cc0
    c2
    cexp
    oveq1
    sq0
    syl6eq
end
