include "cfn.mm"
include "wcel.mm"
include "cdm.mm"
include "cvv.mm"
include "cres.mm"
include "cdom.mm"
include "dmresv.mm"
include "wbr.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "cmpt.mm"
include "wfo.mm"
include "finresfin.mm"
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
include "fodomfi.mm"
include "sylancl.mm"
include "wss.mm"
include "resss.mm"
include "ssdomg.mm"
include "mpi.mm"
include "domtr.mm"
include "syl2anc.mm"
include "syl5eqbrr.mm"

theorem fidomdm
  let cF: class F
  let vx: setvar x


  assert |- ( F e. Fin -> dom F ~<_ F )

  proof
    cF
    cfn
    wcel
    #
    cF
    cdm
    cF
    cvv
    cres
    #
    cdm
    #
    cF
    cdom
    cF
    dmresv
    @0
    @2
    @1
    cdom
    wbr
    #
    @1
    cF
    cdom
    wbr
    #
    @2
    cF
    cdom
    wbr
    @0
    @1
    cfn
    wcel
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
    cvv
    cF
    finresfin
    @8
    @1
    @7
    crn
    #
    @7
    wfo
    #
    @7
    @1
    wfn
    @10
    vx
    @1
    @6
    @7
    @5
    c1st
    fvex
    @7
    eqid
    fnmpti
    @1
    @7
    dffn4
    mpbi
    @1
    wrel
    @2
    @9
    wceq
    @8
    @10
    wb
    cF
    cvv
    relres
    vx
    @1
    reldm
    @2
    @9
    @1
    @7
    foeq3
    mp2b
    mpbir
    @1
    @2
    @7
    fodomfi
    sylancl
    @0
    @1
    cF
    wss
    @4
    cF
    cvv
    resss
    @1
    cF
    cfn
    ssdomg
    mpi
    @2
    @1
    cF
    domtr
    syl2anc
    syl5eqbrr
end
