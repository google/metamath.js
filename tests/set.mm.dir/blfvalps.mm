include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "cxr.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "cmpt2.mm"
include "cvv.mm"
include "cbl.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-bl.mm"
include "a1i.mm"
include "wa.mm"
include "dmeq.mm"
include "dmeqd.mm"
include "psmetdmdm.mm"
include "eqcomd.mm"
include "sylan9eqr.mm"
include "eqidd.mm"
include "simpr.mm"
include "oveqd.mm"
include "breq1d.mm"
include "rabeqbidv.mm"
include "mpt2eq123dv.mm"
include "elex.mm"
include "cxp.mm"
include "cpw.mm"
include "wf.mm"
include "wral.mm"
include "wss.mm"
include "ssrab2.mm"
include "wb.mm"
include "elfvdm.mm"
include "adantr.mm"
include "elpw2g.mm"
include "syl.mm"
include "mpbiri.mm"
include "ralrimivva.mm"
include "eqid.mm"
include "fmpt2.mm"
include "sylib.mm"
include "xrex.mm"
include "xpexg.mm"
include "sylancl.mm"
include "pwexg.mm"
include "fex2.mm"
include "syl3anc.mm"
include "fvmptd.mm"

theorem blfvalps
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cX: class X
  let vr: setvar r
  let vd: setvar d

  disjoint r x
  disjoint r y
  disjoint D r
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint X r
  disjoint X x
  disjoint X y
  disjoint d r
  disjoint d x
  disjoint d y
  disjoint D d
  disjoint X d
  assert |- ( D e. ( PsMet ` X ) -> ( ball ` D ) = ( x e. X , r e. RR* |-> { y e. X | ( x D y ) < r } ) )

  proof
    cD
    cX
    cpsmet
    cfv
    #
    wcel
    #
    vd
    cD
    vx
    vr
    vd
    cv
    #
    cdm
    #
    cdm
    #
    cxr
    vx
    cv
    #
    vy
    cv
    #
    @2
    co
    #
    vr
    cv
    #
    clt
    wbr
    #
    vy
    @4
    crab
    #
    cmpt2
    #
    vx
    vr
    cX
    cxr
    @5
    @6
    cD
    co
    #
    @8
    clt
    wbr
    #
    vy
    cX
    crab
    #
    cmpt2
    #
    cvv
    cbl
    cvv
    cbl
    vd
    cvv
    @11
    cmpt
    wceq
    @1
    vx
    vy
    vr
    vd
    df-bl
    a1i
    @1
    @2
    cD
    wceq
    #
    wa
    #
    vx
    vr
    @4
    cxr
    @10
    cX
    cxr
    @14
    @16
    @1
    @4
    cD
    cdm
    #
    cdm
    #
    cX
    @16
    @3
    @18
    @2
    cD
    dmeq
    dmeqd
    @1
    cX
    @19
    cD
    cX
    psmetdmdm
    eqcomd
    sylan9eqr
    #
    @17
    cxr
    eqidd
    @17
    @9
    @13
    vy
    @4
    cX
    @20
    @17
    @7
    @12
    @8
    clt
    @17
    @2
    cD
    @5
    @6
    @1
    @16
    simpr
    oveqd
    breq1d
    rabeqbidv
    mpt2eq123dv
    cD
    @0
    elex
    @1
    cX
    cxr
    cxp
    #
    cX
    cpw
    #
    @15
    wf
    #
    @21
    cvv
    wcel
    #
    @22
    cvv
    wcel
    #
    @15
    cvv
    wcel
    @1
    @14
    @22
    wcel
    #
    vr
    cxr
    wral
    vx
    cX
    wral
    @23
    @1
    @26
    vx
    vr
    cX
    cxr
    @1
    @5
    cX
    wcel
    @8
    cxr
    wcel
    wa
    #
    wa
    #
    @26
    @14
    cX
    wss
    #
    @13
    vy
    cX
    ssrab2
    @28
    cX
    cpsmet
    cdm
    #
    wcel
    #
    @26
    @29
    wb
    @1
    @31
    @27
    cD
    cX
    cpsmet
    elfvdm
    #
    adantr
    @14
    cX
    @30
    elpw2g
    syl
    mpbiri
    ralrimivva
    vx
    vr
    cX
    cxr
    @14
    @22
    @15
    @15
    eqid
    fmpt2
    sylib
    @1
    @31
    cxr
    cvv
    wcel
    @24
    @32
    xrex
    cX
    cxr
    @30
    cvv
    xpexg
    sylancl
    @1
    @31
    @25
    @32
    cX
    @30
    pwexg
    syl
    @21
    @22
    @15
    cvv
    cvv
    fex2
    syl3anc
    fvmptd
end
