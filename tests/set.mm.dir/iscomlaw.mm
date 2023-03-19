include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "ccomlaw.mm"
include "wa.mm"
include "simpr.mm"
include "wb.mm"
include "oveq.mm"
include "eqeq12d.mm"
include "adantr.mm"
include "raleqbidv.mm"
include "df-comlaw.mm"
include "brabga.mm"

theorem iscomlaw
  let vx: setvar x
  let vy: setvar y
  let cM: class M
  let cV: class V
  let cW: class W
  let c.op: class .o.
  let vm: setvar m
  let vo: setvar o
  let vk: setvar k

  disjoint M x
  disjoint M y
  disjoint x y
  disjoint .o. x
  disjoint .o. y
  disjoint M m
  disjoint M o
  disjoint m o
  disjoint m x
  disjoint m y
  disjoint o x
  disjoint o y
  disjoint .o. m
  disjoint .o. o
  disjoint k x
  assert |- ( ( .o. e. V /\ M e. W ) -> ( .o. comLaw M <-> A. x e. M A. y e. M ( x .o. y ) = ( y .o. x ) ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    vo
    cv
    #
    co
    #
    @1
    @0
    @2
    co
    #
    wceq
    #
    vy
    vm
    cv
    #
    wral
    #
    vx
    @6
    wral
    @0
    @1
    c.op
    co
    #
    @1
    @0
    c.op
    co
    #
    wceq
    #
    vy
    cM
    wral
    #
    vx
    cM
    wral
    vo
    vm
    c.op
    cM
    ccomlaw
    cV
    cW
    @2
    c.op
    wceq
    #
    @6
    cM
    wceq
    #
    wa
    #
    @7
    @11
    vx
    @6
    cM
    @12
    @13
    simpr
    #
    @14
    @5
    @10
    vy
    @6
    cM
    @15
    @12
    @5
    @10
    wb
    @13
    @12
    @3
    @8
    @4
    @9
    @0
    @1
    @2
    c.op
    oveq
    @1
    @0
    @2
    c.op
    oveq
    eqeq12d
    adantr
    raleqbidv
    raleqbidv
    vx
    vy
    vm
    vo
    df-comlaw
    brabga
end
