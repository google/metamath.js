include "cv.mm"
include "wtr.mm"
include "cpw.mm"
include "wcel.mm"
include "cpr.mm"
include "wral.mm"
include "crn.mm"
include "cuni.mm"
include "cmap.mm"
include "co.mm"
include "w3a.mm"
include "wa.mm"
include "cgru.mm"
include "wceq.mm"
include "treq.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "oveq1.mm"
include "raleqbidv.mm"
include "3anbi123d.mm"
include "anbi12d.mm"
include "df-gru.mm"
include "elab2g.mm"

theorem elgrug
  let vx: setvar x
  let vy: setvar y
  let cU: class U
  let cV: class V
  let vu: setvar u

  disjoint U x
  disjoint U y
  disjoint x y
  disjoint U u
  disjoint u x
  disjoint u y
  assert |- ( U e. V -> ( U e. Univ <-> ( Tr U /\ A. x e. U ( ~P x e. U /\ A. y e. U { x , y } e. U /\ A. y e. ( U ^m x ) U. ran y e. U ) ) ) )

  proof
    vu
    cv
    #
    wtr
    #
    vx
    cv
    #
    cpw
    #
    @0
    wcel
    #
    @2
    vy
    cv
    #
    cpr
    #
    @0
    wcel
    #
    vy
    @0
    wral
    #
    @5
    crn
    cuni
    #
    @0
    wcel
    #
    vy
    @0
    @2
    cmap
    co
    #
    wral
    #
    w3a
    #
    vx
    @0
    wral
    #
    wa
    cU
    wtr
    #
    @3
    cU
    wcel
    #
    @6
    cU
    wcel
    #
    vy
    cU
    wral
    #
    @9
    cU
    wcel
    #
    vy
    cU
    @2
    cmap
    co
    #
    wral
    #
    w3a
    #
    vx
    cU
    wral
    #
    wa
    vu
    cU
    cgru
    cV
    @0
    cU
    wceq
    #
    @1
    @15
    @14
    @23
    @0
    cU
    treq
    @13
    @22
    vx
    @0
    cU
    @24
    @4
    @16
    @8
    @18
    @12
    @21
    @0
    cU
    @3
    eleq2
    @7
    @17
    vy
    @0
    cU
    @0
    cU
    @6
    eleq2
    raleqbi1dv
    @24
    @10
    @19
    vy
    @11
    @20
    @0
    cU
    @2
    cmap
    oveq1
    @0
    cU
    @9
    eleq2
    raleqbidv
    3anbi123d
    raleqbi1dv
    anbi12d
    vx
    vy
    vu
    df-gru
    elab2g
end
