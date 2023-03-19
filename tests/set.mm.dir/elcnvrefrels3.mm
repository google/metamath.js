include "cv.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "crn.mm"
include "wral.mm"
include "cdm.mm"
include "crels.mm"
include "ccnvrefrels.mm"
include "dfcnvrefrels3.mm"
include "dmeq.mm"
include "rneq.mm"
include "breq.mm"
include "imbi1d.mm"
include "raleqbidv.mm"
include "rabeqel.mm"

theorem elcnvrefrels3
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
  assert |- ( R e. CnvRefRels <-> ( A. x e. dom R A. y e. ran R ( x R y -> x = y ) /\ R e. Rels ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    vr
    cv
    #
    wbr
    #
    @0
    @1
    wceq
    #
    wi
    #
    vy
    @2
    crn
    #
    wral
    #
    vx
    @2
    cdm
    #
    wral
    @0
    @1
    cR
    wbr
    #
    @4
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
    ccnvrefrels
    cR
    vx
    vy
    vr
    dfcnvrefrels3
    @2
    cR
    wceq
    #
    @7
    @12
    vx
    @8
    @13
    @2
    cR
    dmeq
    @14
    @5
    @10
    vy
    @6
    @11
    @2
    cR
    rneq
    @14
    @3
    @9
    @4
    @0
    @1
    @2
    cR
    breq
    imbi1d
    raleqbidv
    raleqbidv
    rabeqel
end
