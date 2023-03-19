include "cpjh.mm"
include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "chil.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "cch.mm"
include "wss.mm"
include "elpjch.mm"
include "simpld.mm"
include "chss.mm"
include "syl.mm"
include "sseld.mm"
include "wrex.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "cho.mm"
include "elpjhmop.mm"
include "hmopf.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "ccom.mm"
include "fvco3.mm"
include "sylan.mm"
include "elpjidm.mm"
include "adantr.mm"
include "fveq1d.mm"
include "eqtr3d.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "jcad.mm"
include "fnfvelrn.mm"
include "eleq1.mm"
include "expimpd.mm"
include "impbid.mm"
include "abbi2dv.mm"
include "df-rab.mm"
include "syl6eqr.mm"

theorem elpjrn
  let vx: setvar x
  let cT: class T
  let vy: setvar y

  disjoint T x
  disjoint x y
  disjoint T y
  assert |- ( T e. ran projh -> ran T = { x e. ~H | ( T ` x ) = x } )

  proof
    cT
    cpjh
    crn
    wcel
    #
    cT
    crn
    #
    vx
    cv
    #
    chil
    wcel
    #
    @2
    cT
    cfv
    #
    @2
    wceq
    #
    wa
    #
    vx
    cab
    @5
    vx
    chil
    crab
    @0
    @6
    vx
    @1
    @0
    @2
    @1
    wcel
    #
    @6
    @0
    @7
    @3
    @5
    @0
    @1
    chil
    @2
    @0
    @1
    cch
    wcel
    #
    @1
    chil
    wss
    @0
    @8
    cT
    @1
    cpjh
    cfv
    wceq
    cT
    elpjch
    simpld
    @1
    chss
    syl
    sseld
    @0
    @7
    vy
    cv
    #
    cT
    cfv
    #
    @2
    wceq
    #
    vy
    chil
    wrex
    #
    @5
    @0
    cT
    chil
    wfn
    #
    @7
    @12
    wb
    @0
    chil
    chil
    cT
    wf
    #
    @13
    @0
    cT
    cho
    wcel
    @14
    cT
    elpjhmop
    cT
    hmopf
    syl
    #
    chil
    chil
    cT
    ffn
    syl
    #
    vy
    chil
    @2
    cT
    fvelrnb
    syl
    @0
    @11
    @5
    vy
    chil
    @0
    @9
    chil
    wcel
    #
    wa
    #
    @10
    cT
    cfv
    #
    @10
    wceq
    @11
    @5
    @18
    @9
    cT
    cT
    ccom
    #
    cfv
    #
    @19
    @10
    @0
    @14
    @17
    @21
    @19
    wceq
    @15
    chil
    chil
    @9
    cT
    cT
    fvco3
    sylan
    @18
    @9
    @20
    cT
    @0
    @20
    cT
    wceq
    @17
    cT
    elpjidm
    adantr
    fveq1d
    eqtr3d
    @11
    @19
    @4
    @10
    @2
    @10
    @2
    cT
    fveq2
    @11
    id
    eqeq12d
    syl5ibcom
    rexlimdva
    sylbid
    jcad
    @0
    @3
    @5
    @7
    @0
    @3
    wa
    @4
    @1
    wcel
    #
    @5
    @7
    @0
    @13
    @3
    @22
    @16
    chil
    @2
    cT
    fnfvelrn
    sylan
    @4
    @2
    @1
    eleq1
    syl5ibcom
    expimpd
    impbid
    abbi2dv
    @5
    vx
    chil
    df-rab
    syl6eqr
end
