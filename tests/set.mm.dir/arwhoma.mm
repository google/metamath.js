include "wcel.mm"
include "cv.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wrex.mm"
include "cdoma.mm"
include "ccoda.mm"
include "cxp.mm"
include "crn.mm"
include "cuni.mm"
include "arwval.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "cvv.mm"
include "cpw.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "eqid.mm"
include "arwrcl.mm"
include "homaf.mm"
include "ffn.mm"
include "fnunirn.mm"
include "3syl.mm"
include "mpbid.mm"
include "cop.mm"
include "wceq.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "rexxp.mm"
include "sylib.mm"
include "id.mm"
include "homadm.mm"
include "homacd.mm"
include "oveq12d.mm"
include "eleqtrrd.mm"
include "rexlimivw.mm"
include "syl.mm"

theorem arwhoma
  let cA: class A
  let cC: class C
  let cF: class F
  let cH: class H
  let vx: setvar x
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  assume arwrcl.a: |- A = ( Arrow ` C )
  assume arwhoma.h: |- H = ( HomA ` C )


  assert |- ( F e. A -> F e. ( ( domA ` F ) H ( codA ` F ) ) )

  proof
    cF
    cA
    wcel
    #
    cF
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    wcel
    #
    vy
    cC
    cbs
    cfv
    #
    wrex
    #
    vx
    @5
    wrex
    #
    cF
    cF
    cdoma
    cfv
    #
    cF
    ccoda
    cfv
    #
    cH
    co
    #
    wcel
    #
    @0
    cF
    vz
    cv
    #
    cH
    cfv
    #
    wcel
    #
    vz
    @5
    @5
    cxp
    #
    wrex
    #
    @7
    @0
    cF
    cH
    crn
    cuni
    #
    wcel
    #
    @16
    @0
    @18
    cA
    @17
    cF
    cA
    cC
    cH
    arwrcl.a
    arwhoma.h
    arwval
    eleq2i
    biimpi
    @0
    @15
    @15
    cvv
    cxp
    cpw
    #
    cH
    wf
    cH
    @15
    wfn
    @18
    @16
    wb
    @0
    @5
    cC
    cH
    arwhoma.h
    @5
    eqid
    cA
    cC
    cF
    arwrcl.a
    arwrcl
    homaf
    @15
    @19
    cH
    ffn
    vz
    cF
    cH
    @15
    fnunirn
    3syl
    mpbid
    @14
    @4
    vz
    vx
    vy
    @5
    @5
    @12
    @1
    @2
    cop
    #
    wceq
    #
    @13
    @3
    cF
    @21
    @13
    @20
    cH
    cfv
    @3
    @12
    @20
    cH
    fveq2
    @1
    @2
    cH
    df-ov
    syl6eqr
    eleq2d
    rexxp
    sylib
    @6
    @11
    vx
    @5
    @4
    @11
    vy
    @5
    @4
    cF
    @3
    @10
    @4
    id
    @4
    @8
    @1
    @9
    @2
    cH
    cC
    cF
    cH
    @1
    @2
    arwhoma.h
    homadm
    cC
    cF
    cH
    @1
    @2
    arwhoma.h
    homacd
    oveq12d
    eleqtrrd
    rexlimivw
    rexlimivw
    syl
end
