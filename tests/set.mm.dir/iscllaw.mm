include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wral.mm"
include "ccllaw.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "oveq.mm"
include "adantr.mm"
include "eleq12d.mm"
include "raleqbidv.mm"
include "df-cllaw.mm"
include "brabga.mm"

theorem iscllaw
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
  assert |- ( ( .o. e. V /\ M e. W ) -> ( .o. clLaw M <-> A. x e. M A. y e. M ( x .o. y ) e. M ) )

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
    vm
    cv
    #
    wcel
    #
    vy
    @4
    wral
    #
    vx
    @4
    wral
    @0
    @1
    c.op
    co
    #
    cM
    wcel
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
    ccllaw
    cV
    cW
    @2
    c.op
    wceq
    #
    @4
    cM
    wceq
    #
    wa
    #
    @6
    @9
    vx
    @4
    cM
    @10
    @11
    simpr
    #
    @12
    @5
    @8
    vy
    @4
    cM
    @13
    @12
    @3
    @7
    @4
    cM
    @10
    @3
    @7
    wceq
    @11
    @0
    @1
    @2
    c.op
    oveq
    adantr
    @13
    eleq12d
    raleqbidv
    raleqbidv
    vx
    vy
    vm
    vo
    df-cllaw
    brabga
end
