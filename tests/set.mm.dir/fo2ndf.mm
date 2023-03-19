include "wf.mm"
include "crn.mm"
include "c2nd.mm"
include "cres.mm"
include "wceq.mm"
include "wfo.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn3.mm"
include "sylib.mm"
include "f2ndf.mm"
include "syl.mm"
include "wss.mm"
include "sylbi.mm"
include "frn.mm"
include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "wex.mm"
include "elrn2g.mm"
include "ibi.mm"
include "wa.mm"
include "cfv.mm"
include "fvres.mm"
include "adantl.mm"
include "vex.mm"
include "op2nd.mm"
include "syl6req.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "eqeltrd.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "dffo2.mm"
include "sylanbrc.mm"

theorem fo2ndf
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y


  assert |- ( F : A --> B -> ( 2nd |` F ) : F -onto-> ran F )

  proof
    cA
    cB
    cF
    wf
    #
    cF
    cF
    crn
    #
    c2nd
    cF
    cres
    #
    wf
    #
    @2
    crn
    #
    @1
    wceq
    cF
    @1
    @2
    wfo
    @0
    cA
    @1
    cF
    wf
    #
    @3
    @0
    cF
    cA
    wfn
    #
    @5
    cA
    cB
    cF
    ffn
    #
    cA
    cF
    dffn3
    #
    sylib
    cA
    @1
    cF
    f2ndf
    #
    syl
    @0
    @4
    @1
    @0
    @3
    @4
    @1
    wss
    @0
    @6
    @3
    @7
    @6
    @5
    @3
    @8
    @9
    sylbi
    syl
    cF
    @1
    @2
    frn
    syl
    @0
    vy
    @1
    @4
    vy
    cv
    #
    @1
    wcel
    #
    vx
    cv
    #
    @10
    cop
    #
    cF
    wcel
    #
    vx
    wex
    #
    @0
    @10
    @4
    wcel
    #
    @11
    @15
    vx
    @10
    cF
    @1
    elrn2g
    ibi
    @0
    @14
    @16
    vx
    @0
    @14
    @16
    @0
    @14
    wa
    #
    @10
    @13
    @2
    cfv
    #
    @4
    @17
    @18
    @13
    c2nd
    cfv
    #
    @10
    @14
    @18
    @19
    wceq
    @0
    @13
    cF
    c2nd
    fvres
    adantl
    @12
    @10
    vx
    vex
    vy
    vex
    op2nd
    syl6req
    @0
    @2
    cF
    wfn
    #
    @14
    @18
    @4
    wcel
    @0
    cF
    cB
    @2
    wf
    @20
    cA
    cB
    cF
    f2ndf
    cF
    cB
    @2
    ffn
    syl
    cF
    @13
    @2
    fnfvelrn
    sylan
    eqeltrd
    ex
    exlimdv
    syl5
    ssrdv
    eqssd
    cF
    @1
    @2
    dffo2
    sylanbrc
end
