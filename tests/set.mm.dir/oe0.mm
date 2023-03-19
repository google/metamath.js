include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "coe.mm"
include "co.mm"
include "c1o.mm"
include "wceq.mm"
include "oveq1.mm"
include "oe0m0.mm"
include "syl6eq.mm"
include "adantl.mm"
include "wa.mm"
include "cvv.mm"
include "cv.mm"
include "comu.mm"
include "cmpt.mm"
include "crdg.mm"
include "cfv.mm"
include "0elon.mm"
include "oevn0.mm"
include "mpanl2.mm"
include "1on.mm"
include "elexi.mm"
include "rdg0.mm"
include "adantll.mm"
include "oe0lem.mm"
include "anidms.mm"

theorem oe0
  let cA: class A
  let vx: setvar x


  assert |- ( A e. On -> ( A ^o (/) ) = 1o )

  proof
    cA
    con0
    wcel
    #
    cA
    c0
    coe
    co
    #
    c1o
    wceq
    #
    @0
    @2
    cA
    cA
    c0
    wceq
    #
    @2
    @0
    @3
    @1
    c0
    c0
    coe
    co
    c1o
    cA
    c0
    c0
    coe
    oveq1
    oe0m0
    syl6eq
    adantl
    @0
    c0
    cA
    wcel
    #
    @2
    @0
    @0
    @4
    wa
    @1
    c0
    vx
    cvv
    vx
    cv
    cA
    comu
    co
    cmpt
    #
    c1o
    crdg
    cfv
    #
    c1o
    @0
    c0
    con0
    wcel
    @4
    @1
    @6
    wceq
    0elon
    vx
    cA
    c0
    oevn0
    mpanl2
    c1o
    @5
    c1o
    con0
    1on
    elexi
    rdg0
    syl6eq
    adantll
    oe0lem
    anidms
end
