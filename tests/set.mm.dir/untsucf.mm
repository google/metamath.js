include "wel.mm"
include "wn.mm"
include "wral.mm"
include "csuc.mm"
include "nfv.mm"
include "nfral.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "vex.mm"
include "elsuc.mm"
include "elequ1.mm"
include "elequ2.mm"
include "bitrd.mm"
include "notbid.mm"
include "rspccv.mm"
include "untelirr.mm"
include "eleq1.mm"
include "eleq2.mm"
include "syl5ibrcom.mm"
include "jaod.mm"
include "syl5bi.mm"
include "ralrimi.mm"

theorem untsucf
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume untsucf.1: |- F/_ y A

  disjoint A x
  disjoint x y
  assert |- ( A. x e. A -. x e. x -> A. y e. suc A -. y e. y )

  proof
    vx
    vx
    wel
    #
    wn
    #
    vx
    cA
    wral
    #
    vy
    vy
    wel
    #
    wn
    #
    vy
    cA
    csuc
    #
    @1
    vy
    vx
    cA
    untsucf.1
    @1
    vy
    nfv
    nfral
    vy
    cv
    #
    @5
    wcel
    @6
    cA
    wcel
    #
    @6
    cA
    wceq
    #
    wo
    @2
    @4
    @6
    cA
    vy
    vex
    elsuc
    @2
    @7
    @4
    @8
    @1
    @4
    vx
    @6
    cA
    vx
    cv
    @6
    wceq
    #
    @0
    @3
    @9
    @0
    vy
    vx
    wel
    @3
    vx
    vy
    vx
    elequ1
    vx
    vy
    vy
    elequ2
    bitrd
    notbid
    rspccv
    @2
    @4
    @8
    cA
    cA
    wcel
    #
    wn
    vx
    cA
    untelirr
    @8
    @3
    @10
    @8
    @3
    cA
    @6
    wcel
    @10
    @6
    cA
    @6
    eleq1
    @6
    cA
    cA
    eleq2
    bitrd
    notbid
    syl5ibrcom
    jaod
    syl5bi
    ralrimi
end
