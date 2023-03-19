include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "c1.mm"
include "exp0.mm"
include "oveq1d.mm"
include "fac0.mm"
include "oveq2i.mm"
include "1div1e1.mm"
include "eqtri.mm"
include "syl6eq.mm"

theorem eft0val
  let cA: class A


  assert |- ( A e. CC -> ( ( A ^ 0 ) / ( ! ` 0 ) ) = 1 )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    cexp
    co
    #
    cc0
    cfa
    cfv
    #
    cdiv
    co
    c1
    @2
    cdiv
    co
    #
    c1
    @0
    @1
    c1
    @2
    cdiv
    cA
    exp0
    oveq1d
    @3
    c1
    c1
    cdiv
    co
    c1
    @2
    c1
    c1
    cdiv
    fac0
    oveq2i
    1div1e1
    eqtri
    syl6eq
end
