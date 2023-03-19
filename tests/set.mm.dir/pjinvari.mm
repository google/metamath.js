include "chil.mm"
include "ccom.mm"
include "wf.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cpjh.mm"
include "fveq1i.mm"
include "cch.mm"
include "ffvelrn.mm"
include "pjid.mm"
include "sylancr.mm"
include "syl5req.mm"
include "fvco3.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "wfn.mm"
include "wb.mm"
include "wss.mm"
include "wfo.mm"
include "pjfoi.mm"
include "fof.mm"
include "ax-mp.mm"
include "feq1i.mm"
include "mpbir.mm"
include "chssii.mm"
include "fss.mm"
include "mp2an.mm"
include "hocofni.mm"
include "hocofi.mm"
include "eqfnfv.mm"
include "sylibr.mm"
include "fco.mm"
include "feq1.mm"
include "mpbiri.mm"
include "impbii.mm"

theorem pjinvari
  let cS: class S
  let cT: class T
  let cH: class H
  let vx: setvar x
  assume pjinvar.1: |- S : ~H --> ~H
  assume pjinvar.2: |- H e. CH
  assume pjinvar.3: |- T = ( projh ` H )


  assert |- ( ( S o. T ) : ~H --> H <-> ( S o. T ) = ( T o. ( S o. T ) ) )

  proof
    chil
    cH
    cS
    cT
    ccom
    #
    wf
    #
    @0
    cT
    @0
    ccom
    #
    wceq
    #
    @1
    vx
    cv
    #
    @0
    cfv
    #
    @4
    @2
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    #
    @3
    @1
    @7
    vx
    chil
    @1
    @4
    chil
    wcel
    wa
    #
    @5
    @5
    cT
    cfv
    #
    @6
    @9
    @10
    @5
    cH
    cpjh
    cfv
    #
    cfv
    #
    @5
    @5
    cT
    @11
    pjinvar.3
    fveq1i
    @9
    cH
    cch
    wcel
    @5
    cH
    wcel
    @12
    @5
    wceq
    pjinvar.2
    chil
    cH
    @4
    @0
    ffvelrn
    @5
    cH
    pjid
    sylancr
    syl5req
    chil
    cH
    @4
    cT
    @0
    fvco3
    eqtr4d
    ralrimiva
    @0
    chil
    wfn
    @2
    chil
    wfn
    @3
    @8
    wb
    cS
    cT
    pjinvar.1
    chil
    cH
    cT
    wf
    #
    cH
    chil
    wss
    chil
    chil
    cT
    wf
    @13
    chil
    cH
    @11
    wf
    #
    chil
    cH
    @11
    wfo
    @14
    cH
    pjinvar.2
    pjfoi
    chil
    cH
    @11
    fof
    ax-mp
    chil
    cH
    cT
    @11
    pjinvar.3
    feq1i
    mpbir
    #
    cH
    pjinvar.2
    chssii
    chil
    cH
    chil
    cT
    fss
    mp2an
    #
    hocofni
    cT
    @0
    @16
    cS
    cT
    pjinvar.1
    @16
    hocofi
    #
    hocofni
    vx
    chil
    @0
    @2
    eqfnfv
    mp2an
    sylibr
    @3
    @1
    chil
    cH
    @2
    wf
    #
    @13
    chil
    chil
    @0
    wf
    @18
    @15
    @17
    chil
    chil
    cH
    cT
    @0
    fco
    mp2an
    chil
    cH
    @0
    @2
    feq1
    mpbiri
    impbii
end
