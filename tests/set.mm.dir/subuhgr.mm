include "cuhgr.mm"
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
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wfun.mm"
include "subgruhgrfun.mm"
include "ancoms.mm"
include "adantl.mm"
include "funfn.mm"
include "sylib.mm"
include "cv.mm"
include "wral.mm"
include "simplrr.mm"
include "simplrl.mm"
include "simpr.mm"
include "subgruhgredgd.mm"
include "ralrimiva.mm"
include "fnfvrnss.mm"
include "syl2anc.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "wb.mm"
include "cvv.mm"
include "subgrv.mm"
include "isuhgr.mm"
include "adantr.mm"
include "syl.mm"
include "mpbird.mm"
include "ex.mm"
include "anabsi8.mm"

theorem subuhgr
  let cS: class S
  let cG: class G
  let vx: setvar x


  assert |- ( ( G e. UHGraph /\ S SubGraph G ) -> S e. UHGraph )

  proof
    cG
    cuhgr
    wcel
    #
    cS
    cG
    csubgr
    wbr
    #
    cS
    cuhgr
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
    @8
    c0
    csn
    cdif
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
    @13
    @5
    wfun
    #
    @17
    @10
    @19
    @9
    @0
    @1
    @19
    cS
    cG
    subgruhgrfun
    ancoms
    adantl
    @5
    funfn
    sylib
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
    cS
    cG
    @5
    @3
    @21
    @11
    @12
    @9
    @1
    @0
    @23
    simplrr
    @9
    @1
    @0
    @23
    simplrl
    @13
    @23
    simpr
    subgruhgredgd
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
    @10
    @2
    @16
    wb
    #
    @9
    @1
    @24
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
    cvv
    @5
    cS
    @3
    @11
    @12
    isuhgr
    adantr
    syl
    adantr
    adantl
    mpbird
    ex
    syl
    anabsi8
end
