include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "casslaw.mm"
include "wa.mm"
include "simpr.mm"
include "wb.mm"
include "id.mm"
include "oveq.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "adantr.mm"
include "raleqbidv.mm"
include "df-asslaw.mm"
include "brabga.mm"

theorem isasslaw
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  let cV: class V
  let cW: class W
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
  assert |- ( ( .o. e. V /\ M e. W ) -> ( .o. assLaw M <-> A. x e. M A. y e. M A. z e. M ( ( x .o. y ) .o. z ) = ( x .o. ( y .o. z ) ) ) )

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
    vz
    cv
    #
    @2
    co
    #
    @0
    @1
    @4
    @2
    co
    #
    @2
    co
    #
    wceq
    #
    vz
    vm
    cv
    #
    wral
    #
    vy
    @9
    wral
    #
    vx
    @9
    wral
    @0
    @1
    c.op
    co
    #
    @4
    c.op
    co
    #
    @0
    @1
    @4
    c.op
    co
    #
    c.op
    co
    #
    wceq
    #
    vz
    cM
    wral
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
    casslaw
    cV
    cW
    @2
    c.op
    wceq
    #
    @9
    cM
    wceq
    #
    wa
    #
    @11
    @18
    vx
    @9
    cM
    @19
    @20
    simpr
    #
    @21
    @10
    @17
    vy
    @9
    cM
    @22
    @21
    @8
    @16
    vz
    @9
    cM
    @22
    @19
    @8
    @16
    wb
    @20
    @19
    @5
    @13
    @7
    @15
    @19
    @3
    @12
    @4
    @4
    @2
    c.op
    @19
    id
    #
    @0
    @1
    @2
    c.op
    oveq
    @19
    @4
    eqidd
    oveq123d
    @19
    @0
    @0
    @6
    @14
    @2
    c.op
    @23
    @19
    @0
    eqidd
    @1
    @4
    @2
    c.op
    oveq
    oveq123d
    eqeq12d
    adantr
    raleqbidv
    raleqbidv
    raleqbidv
    vx
    vy
    vz
    vm
    vo
    df-asslaw
    brabga
end
