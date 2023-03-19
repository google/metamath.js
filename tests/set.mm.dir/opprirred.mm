include "cir.mm"
include "cfv.mm"
include "cv.mm"
include "cbs.mm"
include "cui.mm"
include "cdif.mm"
include "wcel.mm"
include "cmulr.mm"
include "co.mm"
include "wne.mm"
include "wral.mm"
include "wa.mm"
include "ralcom.mm"
include "eqid.mm"
include "opprmul.mm"
include "neeq1i.mm"
include "2ralbii.mm"
include "bitr4i.mm"
include "anbi2i.mm"
include "isirred.mm"
include "opprbas.mm"
include "opprunit.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem opprirred
  let cR: class R
  let cS: class S
  let cI: class I
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume opprirred.1: |- S = ( oppR ` R )
  assume opprirred.2: |- I = ( Irred ` R )


  assert |- I = ( Irred ` S )

  proof
    vx
    cI
    cS
    cir
    cfv
    #
    vx
    cv
    #
    cR
    cbs
    cfv
    #
    cR
    cui
    cfv
    #
    cdif
    #
    wcel
    #
    vz
    cv
    #
    vy
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    @1
    wne
    #
    vy
    @4
    wral
    vz
    @4
    wral
    #
    wa
    @5
    @7
    @6
    cS
    cmulr
    cfv
    #
    co
    #
    @1
    wne
    #
    vz
    @4
    wral
    vy
    @4
    wral
    #
    wa
    @1
    cI
    wcel
    @1
    @0
    wcel
    @11
    @15
    @5
    @11
    @10
    vz
    @4
    wral
    vy
    @4
    wral
    @15
    @10
    vz
    vy
    @4
    @4
    ralcom
    @14
    @10
    vy
    vz
    @4
    @4
    @13
    @9
    @1
    @2
    cR
    @12
    @8
    cS
    @7
    @6
    @2
    eqid
    #
    @8
    eqid
    #
    opprirred.1
    @12
    eqid
    #
    opprmul
    neeq1i
    2ralbii
    bitr4i
    anbi2i
    vz
    vy
    @2
    cR
    @8
    @3
    cI
    @4
    @1
    @16
    @3
    eqid
    #
    opprirred.2
    @4
    eqid
    #
    @17
    isirred
    vy
    vz
    @2
    cS
    @12
    @3
    @0
    @4
    @1
    @2
    cR
    cS
    opprirred.1
    @16
    opprbas
    cR
    cS
    @3
    @19
    opprirred.1
    opprunit
    @0
    eqid
    @20
    @18
    isirred
    3bitr4i
    eqriv
end
