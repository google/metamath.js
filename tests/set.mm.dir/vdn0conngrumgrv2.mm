include "cconngr.mm"
include "wcel.mm"
include "cumgr.mm"
include "wa.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cvtxdg.mm"
include "cv.mm"
include "ciedg.mm"
include "cdm.mm"
include "crab.mm"
include "cc0.mm"
include "wceq.mm"
include "eqid.mm"
include "vtxdumgrval.mm"
include "ad2ant2lr.mm"
include "wne.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wfn.mm"
include "crn.mm"
include "cuhgr.mm"
include "wfun.mm"
include "umgruhgr.mm"
include "uhgrfun.mm"
include "funfn.mm"
include "biimpi.mm"
include "3syl.mm"
include "adantl.mm"
include "adantr.mm"
include "simpl.mm"
include "simprr.mm"
include "conngrv2edg.mm"
include "syl3anc.mm"
include "eleq2.mm"
include "rexrn.mm"
include "biimpd.mm"
include "sylc.mm"
include "dfrex2.mm"
include "sylib.mm"
include "c0.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "dmex.mm"
include "a1i.mm"
include "rabexg.mm"
include "hasheq0.mm"
include "rabeq0.mm"
include "syl6bb.mm"
include "necon3abid.mm"
include "mpbird.mm"
include "eqnetrd.mm"

theorem vdn0conngrumgrv2
  let cG: class G
  let cN: class N
  let cV: class V
  let ve: setvar e
  let vx: setvar x
  assume vdn0conngrv2.v: |- V = ( Vtx ` G )


  assert |- ( ( ( G e. ConnGraph /\ G e. UMGraph ) /\ ( N e. V /\ 1 < ( # ` V ) ) ) -> ( ( VtxDeg ` G ) ` N ) =/= 0 )

  proof
    cG
    cconngr
    wcel
    #
    cG
    cumgr
    wcel
    #
    wa
    #
    cN
    cV
    wcel
    #
    c1
    cV
    chash
    cfv
    clt
    wbr
    #
    wa
    #
    wa
    #
    cN
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    cN
    vx
    cv
    cG
    ciedg
    cfv
    #
    cfv
    #
    wcel
    #
    vx
    @9
    cdm
    #
    crab
    #
    chash
    cfv
    #
    cc0
    @1
    @3
    @8
    @14
    wceq
    @0
    @4
    vx
    @12
    @7
    cN
    cG
    @9
    cV
    vdn0conngrv2.v
    @9
    eqid
    #
    @12
    eqid
    @7
    eqid
    vtxdumgrval
    ad2ant2lr
    @6
    @14
    cc0
    wne
    @11
    wn
    vx
    @12
    wral
    #
    wn
    #
    @6
    @11
    vx
    @12
    wrex
    #
    @17
    @6
    @9
    @12
    wfn
    #
    cN
    ve
    cv
    #
    wcel
    #
    ve
    @9
    crn
    wrex
    #
    @18
    @2
    @19
    @5
    @1
    @19
    @0
    @1
    cG
    cuhgr
    wcel
    @9
    wfun
    #
    @19
    cG
    umgruhgr
    @9
    cG
    @15
    uhgrfun
    @23
    @19
    @9
    funfn
    biimpi
    3syl
    adantl
    adantr
    @6
    @0
    @3
    @4
    @22
    @2
    @0
    @5
    @0
    @1
    simpl
    adantr
    @5
    @3
    @2
    @3
    @4
    simpl
    adantl
    @2
    @3
    @4
    simprr
    ve
    cG
    @9
    cN
    cV
    vdn0conngrv2.v
    @15
    conngrv2edg
    syl3anc
    @19
    @22
    @18
    @21
    @11
    ve
    vx
    @12
    @9
    @20
    @10
    cN
    eleq2
    rexrn
    biimpd
    sylc
    @11
    vx
    @12
    dfrex2
    sylib
    @6
    @16
    @14
    cc0
    @6
    @14
    cc0
    wceq
    #
    @13
    c0
    wceq
    #
    @16
    @6
    @12
    cvv
    wcel
    #
    @13
    cvv
    wcel
    @24
    @25
    wb
    @26
    @6
    @9
    cG
    ciedg
    fvex
    dmex
    a1i
    @11
    vx
    @12
    cvv
    rabexg
    @13
    cvv
    hasheq0
    3syl
    @11
    vx
    @12
    rabeq0
    syl6bb
    necon3abid
    mpbird
    eqnetrd
end
