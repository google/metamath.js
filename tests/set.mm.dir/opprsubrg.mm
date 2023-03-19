include "csubrg.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "crg.mm"
include "subrgrcl.mm"
include "opprringb.mm"
include "sylibr.mm"
include "csubg.mm"
include "cur.mm"
include "cmulr.mm"
include "co.mm"
include "wral.mm"
include "w3a.mm"
include "wceq.mm"
include "opprsubg.mm"
include "a1i.mm"
include "eleq2d.mm"
include "wb.mm"
include "ralcom.mm"
include "cbs.mm"
include "eqid.mm"
include "opprmul.mm"
include "eleq1i.mm"
include "2ralbii.mm"
include "bitr4i.mm"
include "3anbi13d.mm"
include "issubrg2.mm"
include "opprbas.mm"
include "oppr1.mm"
include "sylbi.mm"
include "3bitr4d.mm"
include "pm5.21nii.mm"
include "eqriv.mm"

theorem opprsubrg
  let cR: class R
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume opprsubrg.o: |- O = ( oppR ` R )


  assert |- ( SubRing ` R ) = ( SubRing ` O )

  proof
    vx
    cR
    csubrg
    cfv
    #
    cO
    csubrg
    cfv
    #
    vx
    cv
    #
    @0
    wcel
    #
    cR
    crg
    wcel
    #
    @2
    @1
    wcel
    #
    @2
    cR
    subrgrcl
    @5
    cO
    crg
    wcel
    #
    @4
    @2
    cO
    subrgrcl
    cR
    cO
    opprsubrg.o
    opprringb
    #
    sylibr
    @4
    @2
    cR
    csubg
    cfv
    #
    wcel
    #
    cR
    cur
    cfv
    #
    @2
    wcel
    #
    vy
    cv
    #
    vz
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    @2
    wcel
    #
    vz
    @2
    wral
    vy
    @2
    wral
    #
    w3a
    @2
    cO
    csubg
    cfv
    #
    wcel
    #
    @11
    @13
    @12
    cO
    cmulr
    cfv
    #
    co
    #
    @2
    wcel
    #
    vy
    @2
    wral
    vz
    @2
    wral
    #
    w3a
    #
    @3
    @5
    @4
    @9
    @19
    @17
    @23
    @11
    @4
    @8
    @18
    @2
    @8
    @18
    wceq
    @4
    cR
    cO
    opprsubrg.o
    opprsubg
    a1i
    eleq2d
    @17
    @23
    wb
    @4
    @17
    @16
    vy
    @2
    wral
    vz
    @2
    wral
    @23
    @16
    vy
    vz
    @2
    @2
    ralcom
    @22
    @16
    vz
    vy
    @2
    @2
    @21
    @15
    @2
    cR
    cbs
    cfv
    #
    cR
    @20
    @14
    cO
    @13
    @12
    @25
    eqid
    #
    @14
    eqid
    #
    opprsubrg.o
    @20
    eqid
    #
    opprmul
    eleq1i
    2ralbii
    bitr4i
    a1i
    3anbi13d
    vy
    vz
    @2
    @25
    cR
    @14
    @10
    @26
    @10
    eqid
    #
    @27
    issubrg2
    @4
    @6
    @5
    @24
    wb
    @7
    vz
    vy
    @2
    @25
    cO
    @20
    @10
    @25
    cR
    cO
    opprsubrg.o
    @26
    opprbas
    cR
    @10
    cO
    opprsubrg.o
    @29
    oppr1
    @28
    issubrg2
    sylbi
    3bitr4d
    pm5.21nii
    eqriv
end
