include "cv.mm"
include "wceq.mm"
include "wbr.mm"
include "wi.mm"
include "crn.mm"
include "wral.mm"
include "cdm.mm"
include "crels.mm"
include "crefrels.mm"
include "dfrefrels3.mm"
include "dmeq.mm"
include "rneq.mm"
include "breq.mm"
include "imbi2d.mm"
include "raleqbidv.mm"
include "rabeqel.mm"

theorem elrefrels3
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let vr: setvar r

  disjoint R x
  disjoint R y
  disjoint x y
  disjoint R r
  disjoint r x
  disjoint r y
  assert |- ( R e. RefRels <-> ( A. x e. dom R A. y e. ran R ( x = y -> x R y ) /\ R e. Rels ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    wceq
    #
    @0
    @1
    vr
    cv
    #
    wbr
    #
    wi
    #
    vy
    @3
    crn
    #
    wral
    #
    vx
    @3
    cdm
    #
    wral
    @2
    @0
    @1
    cR
    wbr
    #
    wi
    #
    vy
    cR
    crn
    #
    wral
    #
    vx
    cR
    cdm
    #
    wral
    vr
    crels
    crefrels
    cR
    vx
    vy
    vr
    dfrefrels3
    @3
    cR
    wceq
    #
    @7
    @12
    vx
    @8
    @13
    @3
    cR
    dmeq
    @14
    @5
    @10
    vy
    @6
    @11
    @3
    cR
    rneq
    @14
    @4
    @9
    @2
    @0
    @1
    @3
    cR
    breq
    imbi2d
    raleqbidv
    raleqbidv
    rabeqel
end
