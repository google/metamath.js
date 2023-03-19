include "cumgr.mm"
include "wcel.mm"
include "csubgr.mm"
include "wbr.mm"
include "cvtx.mm"
include "cfv.mm"
include "wss.mm"
include "ciedg.mm"
include "cedg.mm"
include "cpw.mm"
include "w3a.mm"
include "wa.mm"
include "wi.mm"
include "eqid.mm"
include "subgrprop2.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "crab.mm"
include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wfun.mm"
include "cuhgr.mm"
include "umgruhgr.mm"
include "subgruhgrfun.mm"
include "sylan.mm"
include "ancoms.mm"
include "funfn.mm"
include "sylib.mm"
include "adantl.mm"
include "wral.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simpr.mm"
include "subumgredg2.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "fnfvrnss.mm"
include "syl2anc.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "wb.mm"
include "cvv.mm"
include "subgrv.mm"
include "isumgrs.mm"
include "adantr.mm"
include "syl.mm"
include "ad2antrl.mm"
include "mpbird.mm"
include "ex.mm"
include "anabsi8.mm"

theorem subumgr
  let cS: class S
  let cG: class G
  let vx: setvar x
  let ve: setvar e


  assert |- ( ( G e. UMGraph /\ S SubGraph G ) -> S e. UMGraph )

  proof
    cG
    cumgr
    wcel
    #
    cS
    cG
    csubgr
    wbr
    #
    cS
    cumgr
    wcel
    #
    @1
    cS
    cvtx
    cfv
    #
    cG
    cvtx
    cfv
    #
    wss
    cS
    ciedg
    cfv
    #
    cG
    ciedg
    cfv
    #
    wss
    cS
    cedg
    cfv
    #
    @3
    cpw
    #
    wss
    w3a
    #
    @1
    @0
    wa
    #
    @2
    wi
    @4
    @6
    cS
    @7
    cG
    @5
    @3
    @3
    eqid
    #
    @4
    eqid
    @5
    eqid
    #
    @6
    eqid
    @7
    eqid
    subgrprop2
    @9
    @10
    @2
    @9
    @10
    wa
    #
    @2
    @5
    cdm
    #
    ve
    cv
    chash
    cfv
    c2
    wceq
    ve
    @8
    crab
    #
    @5
    wf
    #
    @13
    @5
    @14
    wfn
    #
    @5
    crn
    @15
    wss
    #
    @16
    @10
    @17
    @9
    @10
    @5
    wfun
    #
    @17
    @0
    @1
    @19
    @0
    cG
    cuhgr
    wcel
    @1
    @19
    cG
    umgruhgr
    cS
    cG
    subgruhgrfun
    sylan
    ancoms
    @5
    funfn
    sylib
    adantl
    #
    @13
    @17
    vx
    cv
    #
    @5
    cfv
    @15
    wcel
    #
    vx
    @14
    wral
    @18
    @20
    @13
    @22
    vx
    @14
    @13
    @21
    @14
    wcel
    #
    wa
    @1
    @0
    @23
    @22
    @9
    @1
    @0
    @23
    simplrl
    @9
    @1
    @0
    @23
    simplrr
    @13
    @23
    simpr
    cS
    ve
    cG
    @5
    @3
    @21
    @11
    @12
    subumgredg2
    syl3anc
    ralrimiva
    vx
    @14
    @15
    @5
    fnfvrnss
    syl2anc
    @14
    @15
    @5
    df-f
    sylanbrc
    @1
    @2
    @16
    wb
    #
    @9
    @0
    @1
    cS
    cvv
    wcel
    #
    cG
    cvv
    wcel
    #
    wa
    @24
    cS
    cG
    subgrv
    @25
    @24
    @26
    ve
    cvv
    @5
    cS
    @3
    @11
    @12
    isumgrs
    adantr
    syl
    ad2antrl
    mpbird
    ex
    syl
    anabsi8
end
