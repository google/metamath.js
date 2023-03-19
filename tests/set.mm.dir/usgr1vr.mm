include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "cusgr.mm"
include "ciedg.mm"
include "c0.mm"
include "cedg.mm"
include "cuhgr.mm"
include "chash.mm"
include "c1.mm"
include "cdm.mm"
include "c2.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "crab.mm"
include "wf.mm"
include "usgruhgr.mm"
include "adantl.mm"
include "fveq2.mm"
include "hashsng.mm"
include "sylan9eqr.mm"
include "adantr.mm"
include "cuspgr.mm"
include "eqid.mm"
include "usgrislfuspgr.mm"
include "simprbi.mm"
include "lfuhgr1v0e.mm"
include "syl3anc.mm"
include "wb.mm"
include "uhgriedg0edg0.mm"
include "syl.mm"
include "mpbid.mm"
include "ex.mm"

theorem usgr1vr
  let cA: class A
  let cG: class G
  let cX: class X
  let vx: setvar x
  let cW: class W


  assert |- ( ( A e. X /\ ( Vtx ` G ) = { A } ) -> ( G e. USGraph -> ( iEdg ` G ) = (/) ) )

  proof
    cA
    cX
    wcel
    #
    cG
    cvtx
    cfv
    #
    cA
    csn
    #
    wceq
    #
    wa
    #
    cG
    cusgr
    wcel
    #
    cG
    ciedg
    cfv
    #
    c0
    wceq
    #
    @4
    @5
    wa
    #
    cG
    cedg
    cfv
    c0
    wceq
    #
    @7
    @8
    cG
    cuhgr
    wcel
    #
    @1
    chash
    cfv
    #
    c1
    wceq
    #
    @6
    cdm
    c2
    vx
    cv
    chash
    cfv
    cle
    wbr
    vx
    @1
    cpw
    crab
    #
    @6
    wf
    #
    @9
    @5
    @10
    @4
    cG
    usgruhgr
    #
    adantl
    @4
    @12
    @5
    @3
    @0
    @11
    @2
    chash
    cfv
    c1
    @1
    @2
    chash
    fveq2
    cA
    cX
    hashsng
    sylan9eqr
    adantr
    @5
    @14
    @4
    @5
    cG
    cuspgr
    wcel
    @14
    vx
    cG
    @6
    @1
    @1
    eqid
    #
    @6
    eqid
    #
    usgrislfuspgr
    simprbi
    adantl
    vx
    @13
    cG
    @6
    @1
    @16
    @17
    @13
    eqid
    lfuhgr1v0e
    syl3anc
    @5
    @9
    @7
    wb
    #
    @4
    @5
    @10
    @18
    @15
    cG
    uhgriedg0edg0
    syl
    adantl
    mpbid
    ex
end
