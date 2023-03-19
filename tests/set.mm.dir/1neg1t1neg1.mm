include "c1.mm"
include "cneg.mm"
include "cpr.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "cmul.mm"
include "co.mm"
include "elpri.mm"
include "id.mm"
include "oveq12d.mm"
include "neg1mulneg1e1.mm"
include "syl6eq.mm"
include "1t1e1.mm"
include "jaoi.mm"
include "syl.mm"

theorem 1neg1t1neg1
  let cN: class N


  assert |- ( N e. { -u 1 , 1 } -> ( N x. N ) = 1 )

  proof
    cN
    c1
    cneg
    #
    c1
    cpr
    wcel
    cN
    @0
    wceq
    #
    cN
    c1
    wceq
    #
    wo
    cN
    cN
    cmul
    co
    #
    c1
    wceq
    #
    cN
    @0
    c1
    elpri
    @1
    @4
    @2
    @1
    @3
    @0
    @0
    cmul
    co
    c1
    @1
    cN
    @0
    cN
    @0
    cmul
    @1
    id
    #
    @5
    oveq12d
    neg1mulneg1e1
    syl6eq
    @2
    @3
    c1
    c1
    cmul
    co
    c1
    @2
    cN
    c1
    cN
    c1
    cmul
    @2
    id
    #
    @6
    oveq12d
    1t1e1
    syl6eq
    jaoi
    syl
end
