include "casslaw.mm"
include "wbr.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "df-asslaw.mm"
include "bropaex12.mm"
include "isasslaw.mm"
include "syl.mm"
include "ibi.mm"

theorem asslawass
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  let c.op: class .o.
  let vm: setvar m
  let vo: setvar o
  let vk: setvar k

  disjoint M x
  disjoint M y
  disjoint M z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint .o. x
  disjoint .o. y
  disjoint .o. z
  disjoint M m
  disjoint M o
  disjoint m o
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint .o. m
  disjoint .o. o
  disjoint k x
  assert |- ( .o. assLaw M -> A. x e. M A. y e. M A. z e. M ( ( x .o. y ) .o. z ) = ( x .o. ( y .o. z ) ) )

  proof
    c.op
    cM
    casslaw
    wbr
    #
    vx
    cv
    #
    vy
    cv
    #
    c.op
    co
    vz
    cv
    #
    c.op
    co
    @1
    @2
    @3
    c.op
    co
    c.op
    co
    wceq
    vz
    cM
    wral
    vy
    cM
    wral
    vx
    cM
    wral
    #
    @0
    c.op
    cvv
    wcel
    cM
    cvv
    wcel
    wa
    @0
    @4
    wb
    @1
    @2
    vo
    cv
    #
    co
    @3
    @5
    co
    @1
    @2
    @3
    @5
    co
    @5
    co
    wceq
    vz
    vm
    cv
    #
    wral
    vy
    @6
    wral
    vx
    @6
    wral
    vo
    vm
    c.op
    cM
    casslaw
    vx
    vy
    vz
    vm
    vo
    df-asslaw
    bropaex12
    vx
    vy
    vz
    cM
    cvv
    cvv
    c.op
    isasslaw
    syl
    ibi
end
