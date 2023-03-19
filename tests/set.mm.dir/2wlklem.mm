include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "wceq.mm"
include "cc0.mm"
include "c2.mm"
include "c0ex.mm"
include "1ex.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "preq12d.mm"
include "eqeq12d.mm"
include "1p1e2.mm"
include "ralpr.mm"

theorem 2wlklem
  let cP: class P
  let vk: setvar k
  let cE: class E
  let cF: class F

  disjoint E k
  disjoint F k
  disjoint P k
  assert |- ( A. k e. { 0 , 1 } ( E ` ( F ` k ) ) = { ( P ` k ) , ( P ` ( k + 1 ) ) } <-> ( ( E ` ( F ` 0 ) ) = { ( P ` 0 ) , ( P ` 1 ) } /\ ( E ` ( F ` 1 ) ) = { ( P ` 1 ) , ( P ` 2 ) } ) )

  proof
    vk
    cv
    #
    cF
    cfv
    #
    cE
    cfv
    #
    @0
    cP
    cfv
    #
    @0
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    wceq
    cc0
    cF
    cfv
    #
    cE
    cfv
    #
    cc0
    cP
    cfv
    #
    c1
    cP
    cfv
    #
    cpr
    #
    wceq
    c1
    cF
    cfv
    #
    cE
    cfv
    #
    @10
    c2
    cP
    cfv
    #
    cpr
    #
    wceq
    vk
    cc0
    c1
    c0ex
    1ex
    @0
    cc0
    wceq
    #
    @2
    @8
    @6
    @11
    @16
    @1
    @7
    cE
    @0
    cc0
    cF
    fveq2
    fveq2d
    @16
    @3
    @9
    @5
    @10
    @0
    cc0
    cP
    fveq2
    @16
    @4
    c1
    cP
    @16
    @4
    cc0
    c1
    caddc
    co
    c1
    @0
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    fveq2d
    preq12d
    eqeq12d
    @0
    c1
    wceq
    #
    @2
    @13
    @6
    @15
    @17
    @1
    @12
    cE
    @0
    c1
    cF
    fveq2
    fveq2d
    @17
    @3
    @10
    @5
    @14
    @0
    c1
    cP
    fveq2
    @17
    @4
    c2
    cP
    @17
    @4
    c1
    c1
    caddc
    co
    c2
    @0
    c1
    c1
    caddc
    oveq1
    1p1e2
    syl6eq
    fveq2d
    preq12d
    eqeq12d
    ralpr
end
