include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "coe.mm"
include "co.mm"
include "wceq.mm"
include "c1o.mm"
include "cdif.mm"
include "cvv.mm"
include "cv.mm"
include "comu.mm"
include "cmpt.mm"
include "crdg.mm"
include "cfv.mm"
include "cif.mm"
include "0elon.mm"
include "oev.mm"
include "mpan.mm"
include "eqid.mm"
include "iftruei.mm"
include "syl6eq.mm"

theorem oe0m
  let cA: class A
  let vx: setvar x


  assert |- ( A e. On -> ( (/) ^o A ) = ( 1o \ A ) )

  proof
    cA
    con0
    wcel
    #
    c0
    cA
    coe
    co
    #
    c0
    c0
    wceq
    #
    c1o
    cA
    cdif
    #
    cA
    vx
    cvv
    vx
    cv
    c0
    comu
    co
    cmpt
    c1o
    crdg
    cfv
    #
    cif
    #
    @3
    c0
    con0
    wcel
    @0
    @1
    @5
    wceq
    0elon
    vx
    c0
    cA
    oev
    mpan
    @2
    @3
    @4
    c0
    eqid
    iftruei
    syl6eq
end
