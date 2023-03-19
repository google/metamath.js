include "wpo.mm"
include "cv.mm"
include "wbr.mm"
include "weq.mm"
include "w3o.mm"
include "wral.mm"
include "wa.mm"
include "ccnv.mm"
include "wor.mm"
include "cnvpo.mm"
include "ralcom.mm"
include "vex.mm"
include "brcnv.mm"
include "equcom.mm"
include "3orbi123i.mm"
include "2ralbii.mm"
include "bitr4i.mm"
include "anbi12i.mm"
include "df-so.mm"
include "3bitr4i.mm"

theorem cnvso
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R Or A <-> `' R Or A )

  proof
    cA
    cR
    wpo
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    vx
    vy
    weq
    #
    @2
    @1
    cR
    wbr
    #
    w3o
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    cA
    cR
    ccnv
    #
    wpo
    #
    @2
    @1
    @8
    wbr
    #
    vy
    vx
    weq
    #
    @1
    @2
    @8
    wbr
    #
    w3o
    #
    vx
    cA
    wral
    vy
    cA
    wral
    #
    wa
    cA
    cR
    wor
    cA
    @8
    wor
    @0
    @9
    @7
    @14
    cA
    cR
    cnvpo
    @7
    @6
    vx
    cA
    wral
    vy
    cA
    wral
    @14
    @6
    vx
    vy
    cA
    cA
    ralcom
    @13
    @6
    vy
    vx
    cA
    cA
    @10
    @3
    @11
    @4
    @12
    @5
    @2
    @1
    cR
    vy
    vex
    #
    vx
    vex
    #
    brcnv
    vy
    vx
    equcom
    @1
    @2
    cR
    @16
    @15
    brcnv
    3orbi123i
    2ralbii
    bitr4i
    anbi12i
    vx
    vy
    cA
    cR
    df-so
    vy
    vx
    cA
    @8
    df-so
    3bitr4i
end
