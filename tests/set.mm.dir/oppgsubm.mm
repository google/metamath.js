include "csubmnd.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "cmnd.mm"
include "submrcl.mm"
include "oppgmndb.mm"
include "sylibr.mm"
include "cbs.mm"
include "wss.mm"
include "c0g.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "w3a.mm"
include "wb.mm"
include "ralcom.mm"
include "eqid.mm"
include "oppgplus.mm"
include "eleq1i.mm"
include "2ralbii.mm"
include "bitr4i.mm"
include "3anbi3i.mm"
include "a1i.mm"
include "issubm.mm"
include "oppgbas.mm"
include "oppgid.mm"
include "sylbi.mm"
include "3bitr4d.mm"
include "pm5.21nii.mm"
include "eqriv.mm"

theorem oppgsubm
  let cG: class G
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cZ: class Z
  assume oppggic.o: |- O = ( oppG ` G )


  assert |- ( SubMnd ` G ) = ( SubMnd ` O )

  proof
    vx
    cG
    csubmnd
    cfv
    #
    cO
    csubmnd
    cfv
    #
    vx
    cv
    #
    @0
    wcel
    #
    cG
    cmnd
    wcel
    #
    @2
    @1
    wcel
    #
    @2
    cG
    submrcl
    @5
    cO
    cmnd
    wcel
    #
    @4
    @2
    cO
    submrcl
    cG
    cO
    oppggic.o
    oppgmndb
    #
    sylibr
    @4
    @2
    cG
    cbs
    cfv
    #
    wss
    #
    cG
    c0g
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
    cG
    cplusg
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
    #
    @9
    @11
    @13
    @12
    cO
    cplusg
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
    @18
    @23
    wb
    @4
    @17
    @22
    @9
    @11
    @17
    @16
    vy
    @2
    wral
    vz
    @2
    wral
    @22
    @16
    vy
    vz
    @2
    @2
    ralcom
    @21
    @16
    vz
    vy
    @2
    @2
    @20
    @15
    @2
    @14
    @19
    cG
    cO
    @13
    @12
    @14
    eqid
    #
    oppggic.o
    @19
    eqid
    #
    oppgplus
    eleq1i
    2ralbii
    bitr4i
    3anbi3i
    a1i
    vy
    vz
    @8
    @14
    @2
    cG
    @10
    @8
    eqid
    #
    @10
    eqid
    #
    @24
    issubm
    @4
    @6
    @5
    @23
    wb
    @7
    vz
    vy
    @8
    @19
    @2
    cO
    @10
    @8
    cG
    cO
    oppggic.o
    @26
    oppgbas
    cG
    cO
    @10
    oppggic.o
    @27
    oppgid
    @25
    issubm
    sylbi
    3bitr4d
    pm5.21nii
    eqriv
end
