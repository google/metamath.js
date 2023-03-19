include "cpjh.mm"
include "crn.mm"
include "wcel.mm"
include "cho.mm"
include "ccom.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cch.mm"
include "wrex.mm"
include "wfn.mm"
include "wb.mm"
include "pjmfn.mm"
include "fvelrnb.mm"
include "ax-mp.mm"
include "pjhmop.mm"
include "pjidmco.mm"
include "jca.mm"
include "eleq1.mm"
include "id.mm"
include "coeq12d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "hmopidmpj.mm"
include "hmopidmch.mm"
include "fnfvelrn.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "impbii.mm"

theorem dfpjop
  let cT: class T
  let vt: setvar t
  let vx: setvar x


  assert |- ( T e. ran projh <-> ( T e. HrmOp /\ ( T o. T ) = T ) )

  proof
    cT
    cpjh
    crn
    #
    wcel
    #
    cT
    cho
    wcel
    #
    cT
    cT
    ccom
    #
    cT
    wceq
    #
    wa
    #
    @1
    vx
    cv
    #
    cpjh
    cfv
    #
    cT
    wceq
    #
    vx
    cch
    wrex
    #
    @5
    cpjh
    cch
    wfn
    #
    @1
    @9
    wb
    pjmfn
    vx
    cch
    cT
    cpjh
    fvelrnb
    ax-mp
    @8
    @5
    vx
    cch
    @6
    cch
    wcel
    #
    @7
    cho
    wcel
    #
    @7
    @7
    ccom
    #
    @7
    wceq
    #
    wa
    @8
    @5
    @11
    @12
    @14
    @6
    pjhmop
    @6
    pjidmco
    jca
    @8
    @12
    @2
    @14
    @4
    @7
    cT
    cho
    eleq1
    @8
    @13
    @3
    @7
    cT
    @8
    @7
    cT
    @7
    cT
    @8
    id
    #
    @15
    coeq12d
    @15
    eqeq12d
    anbi12d
    syl5ibcom
    rexlimiv
    sylbi
    @5
    cT
    cT
    crn
    #
    cpjh
    cfv
    #
    @0
    cT
    hmopidmpj
    @5
    @10
    @16
    cch
    wcel
    @17
    @0
    wcel
    pjmfn
    cT
    hmopidmch
    cch
    @16
    cpjh
    fnfvelrn
    sylancr
    eqeltrd
    impbii
end
