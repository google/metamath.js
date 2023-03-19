include "wss.mm"
include "cpjh.mm"
include "cfv.mm"
include "chod.mm"
include "co.mm"
include "cort.mm"
include "cin.mm"
include "wceq.mm"
include "cv.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cmv.mm"
include "wf.mm"
include "pjfi.mm"
include "hodval.mm"
include "mp3an12.mm"
include "adantl.mm"
include "pjssmi.mm"
include "impcom.mm"
include "eqtrd.mm"
include "ralrimiva.mm"
include "wfn.mm"
include "wb.mm"
include "hosubfni.mm"
include "choccli.mm"
include "chincli.mm"
include "pjfni.mm"
include "eqfnfv.mm"
include "mp2an.mm"
include "sylibr.mm"
include "cc0.mm"
include "csp.mm"
include "cle.mm"
include "wbr.mm"
include "pjige0i.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "adantr.mm"
include "breqtrrd.mm"
include "pjssposi.mm"
include "sylib.mm"
include "impbii.mm"

theorem pjssdif2i
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjco.1: |- G e. CH
  assume pjco.2: |- H e. CH


  assert |- ( G C_ H <-> ( ( projh ` H ) -op ( projh ` G ) ) = ( projh ` ( H i^i ( _|_ ` G ) ) ) )

  proof
    cG
    cH
    wss
    #
    cH
    cpjh
    cfv
    #
    cG
    cpjh
    cfv
    #
    chod
    co
    #
    cH
    cG
    cort
    cfv
    #
    cin
    #
    cpjh
    cfv
    #
    wceq
    #
    @0
    vx
    cv
    #
    @3
    cfv
    #
    @8
    @6
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    #
    @7
    @0
    @11
    vx
    chil
    @0
    @8
    chil
    wcel
    #
    wa
    @9
    @8
    @1
    cfv
    @8
    @2
    cfv
    cmv
    co
    #
    @10
    @13
    @9
    @14
    wceq
    #
    @0
    chil
    chil
    @1
    wf
    chil
    chil
    @2
    wf
    @13
    @15
    cH
    pjco.2
    pjfi
    #
    cG
    pjco.1
    pjfi
    #
    @8
    @1
    @2
    hodval
    mp3an12
    adantl
    @13
    @0
    @14
    @10
    wceq
    @8
    cH
    cG
    pjco.2
    pjco.1
    pjssmi
    impcom
    eqtrd
    ralrimiva
    @3
    chil
    wfn
    @6
    chil
    wfn
    @7
    @12
    wb
    @1
    @2
    @16
    @17
    hosubfni
    @5
    cH
    @4
    pjco.2
    cG
    pjco.1
    choccli
    chincli
    #
    pjfni
    vx
    chil
    @3
    @6
    eqfnfv
    mp2an
    sylibr
    @7
    cc0
    @9
    @8
    csp
    co
    #
    cle
    wbr
    #
    vx
    chil
    wral
    @0
    @7
    @20
    vx
    chil
    @7
    @13
    wa
    cc0
    @10
    @8
    csp
    co
    #
    @19
    cle
    @13
    cc0
    @21
    cle
    wbr
    @7
    @8
    @5
    @18
    pjige0i
    adantl
    @7
    @19
    @21
    wceq
    @13
    @7
    @9
    @10
    @8
    csp
    @8
    @3
    @6
    fveq1
    oveq1d
    adantr
    breqtrrd
    ralrimiva
    vx
    cG
    cH
    pjco.1
    pjco.2
    pjssposi
    sylib
    impbii
end
