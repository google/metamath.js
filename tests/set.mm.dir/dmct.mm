include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cdm.mm"
include "cvv.mm"
include "cres.mm"
include "dmresv.mm"
include "wcel.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "cmpt.mm"
include "wfo.mm"
include "wss.mm"
include "resss.mm"
include "ctex.mm"
include "ssexg.mm"
include "sylancr.mm"
include "crn.mm"
include "wfn.mm"
include "fvex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "dffn4.mm"
include "mpbi.mm"
include "wrel.mm"
include "wceq.mm"
include "wb.mm"
include "relres.mm"
include "reldm.mm"
include "foeq3.mm"
include "mp2b.mm"
include "mpbir.mm"
include "fodomg.mm"
include "mpisyl.mm"
include "ssdomg.mm"
include "domtr.mm"
include "mpancom.mm"
include "syl2anc.mm"
include "syl5eqbrr.mm"

theorem dmct
  let cA: class A
  let vx: setvar x


  assert |- ( A ~<_ _om -> dom A ~<_ _om )

  proof
    cA
    com
    cdom
    wbr
    #
    cA
    cdm
    cA
    cvv
    cres
    #
    cdm
    #
    com
    cdom
    cA
    dmresv
    @0
    @2
    @1
    cdom
    wbr
    #
    @1
    com
    cdom
    wbr
    #
    @2
    com
    cdom
    wbr
    @0
    @1
    cvv
    wcel
    #
    @1
    @2
    vx
    @1
    vx
    cv
    #
    c1st
    cfv
    #
    cmpt
    #
    wfo
    #
    @3
    @0
    @1
    cA
    wss
    #
    cA
    cvv
    wcel
    #
    @5
    cA
    cvv
    resss
    #
    cA
    ctex
    #
    @1
    cA
    cvv
    ssexg
    sylancr
    @9
    @1
    @8
    crn
    #
    @8
    wfo
    #
    @8
    @1
    wfn
    @15
    vx
    @1
    @7
    @8
    @6
    c1st
    fvex
    @8
    eqid
    fnmpti
    @1
    @8
    dffn4
    mpbi
    @1
    wrel
    @2
    @14
    wceq
    @9
    @15
    wb
    cA
    cvv
    relres
    vx
    @1
    reldm
    @2
    @14
    @1
    @8
    foeq3
    mp2b
    mpbir
    @1
    @2
    cvv
    @8
    fodomg
    mpisyl
    @1
    cA
    cdom
    wbr
    #
    @0
    @4
    @0
    @11
    @10
    @16
    @13
    @12
    @1
    cA
    cvv
    ssdomg
    mpisyl
    @1
    cA
    com
    domtr
    mpancom
    @2
    @1
    com
    domtr
    syl2anc
    syl5eqbrr
end
