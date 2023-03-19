include "wcel.mm"
include "wfn.mm"
include "csn.mm"
include "cres.mm"
include "cfv.mm"
include "cop.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "sneq.mm"
include "reseq2d.mm"
include "fveq2.mm"
include "opeq12.mm"
include "mpdan.mm"
include "sneqd.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "wa.mm"
include "wss.mm"
include "vex.mm"
include "snss.mm"
include "fnssres.mm"
include "sylan2b.mm"
include "cvv.mm"
include "wf.mm"
include "dffn2.mm"
include "fsn2.mm"
include "fvex.mm"
include "biantrur.mm"
include "vsnid.mm"
include "fvres.mm"
include "ax-mp.mm"
include "opeq2i.mm"
include "sneqi.mm"
include "eqeq2i.mm"
include "bitr3i.mm"
include "3bitri.mm"
include "sylib.mm"
include "expcom.mm"
include "vtoclga.mm"
include "impcom.mm"

theorem fnressn
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let cC: class C


  assert |- ( ( F Fn A /\ B e. A ) -> ( F |` { B } ) = { <. B , ( F ` B ) >. } )

  proof
    cB
    cA
    wcel
    cF
    cA
    wfn
    #
    cF
    cB
    csn
    #
    cres
    #
    cB
    cB
    cF
    cfv
    #
    cop
    #
    csn
    #
    wceq
    #
    @0
    cF
    vx
    cv
    #
    csn
    #
    cres
    #
    @7
    @7
    cF
    cfv
    #
    cop
    #
    csn
    #
    wceq
    #
    wi
    @0
    @6
    wi
    vx
    cB
    cA
    @7
    cB
    wceq
    #
    @13
    @6
    @0
    @14
    @9
    @2
    @12
    @5
    @14
    @8
    @1
    cF
    @7
    cB
    sneq
    reseq2d
    @14
    @11
    @4
    @14
    @10
    @3
    wceq
    @11
    @4
    wceq
    @7
    cB
    cF
    fveq2
    @7
    @10
    cB
    @3
    opeq12
    mpdan
    sneqd
    eqeq12d
    imbi2d
    @0
    @7
    cA
    wcel
    #
    @13
    @0
    @15
    wa
    @9
    @8
    wfn
    #
    @13
    @15
    @0
    @8
    cA
    wss
    @16
    @7
    cA
    vx
    vex
    #
    snss
    cA
    @8
    cF
    fnssres
    sylan2b
    @16
    @8
    cvv
    @9
    wf
    @7
    @9
    cfv
    #
    cvv
    wcel
    #
    @9
    @7
    @18
    cop
    #
    csn
    #
    wceq
    #
    wa
    #
    @13
    @8
    @9
    dffn2
    @7
    cvv
    @9
    @17
    fsn2
    @23
    @22
    @13
    @19
    @22
    @7
    @9
    fvex
    biantrur
    @21
    @12
    @9
    @20
    @11
    @18
    @10
    @7
    @7
    @8
    wcel
    @18
    @10
    wceq
    vx
    vsnid
    @7
    @8
    cF
    fvres
    ax-mp
    opeq2i
    sneqi
    eqeq2i
    bitr3i
    3bitri
    sylib
    expcom
    vtoclga
    impcom
end
