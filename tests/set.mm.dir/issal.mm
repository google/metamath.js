include "c0.mm"
include "cv.mm"
include "wcel.mm"
include "cuni.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "cpw.mm"
include "w3a.mm"
include "csalg.mm"
include "wceq.mm"
include "eleq2.mm"
include "id.mm"
include "unieq.mm"
include "difeq1d.mm"
include "eleq12d.mm"
include "raleqbidv.mm"
include "pweq.mm"
include "imbi2d.mm"
include "3anbi123d.mm"
include "df-salg.mm"
include "elab2g.mm"

theorem issal
  let vy: setvar y
  let cS: class S
  let cV: class V
  let vx: setvar x
  let vk: setvar k

  disjoint S y
  disjoint S x
  disjoint x y
  disjoint k x
  assert |- ( S e. V -> ( S e. SAlg <-> ( (/) e. S /\ A. y e. S ( U. S \ y ) e. S /\ A. y e. ~P S ( y ~<_ _om -> U. y e. S ) ) ) )

  proof
    c0
    vx
    cv
    #
    wcel
    #
    @0
    cuni
    #
    vy
    cv
    #
    cdif
    #
    @0
    wcel
    #
    vy
    @0
    wral
    #
    @3
    com
    cdom
    wbr
    #
    @3
    cuni
    #
    @0
    wcel
    #
    wi
    #
    vy
    @0
    cpw
    #
    wral
    #
    w3a
    c0
    cS
    wcel
    #
    cS
    cuni
    #
    @3
    cdif
    #
    cS
    wcel
    #
    vy
    cS
    wral
    #
    @7
    @8
    cS
    wcel
    #
    wi
    #
    vy
    cS
    cpw
    #
    wral
    #
    w3a
    vx
    cS
    csalg
    cV
    @0
    cS
    wceq
    #
    @1
    @13
    @6
    @17
    @12
    @21
    @0
    cS
    c0
    eleq2
    @22
    @5
    @16
    vy
    @0
    cS
    @22
    id
    #
    @22
    @4
    @15
    @0
    cS
    @22
    @2
    @14
    @3
    @0
    cS
    unieq
    difeq1d
    @23
    eleq12d
    raleqbidv
    @22
    @10
    @19
    vy
    @11
    @20
    @0
    cS
    pweq
    @22
    @9
    @18
    @7
    @0
    cS
    @8
    eleq2
    imbi2d
    raleqbidv
    3anbi123d
    vx
    vy
    df-salg
    elab2g
end
