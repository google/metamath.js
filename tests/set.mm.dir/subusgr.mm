include "cusgr.mm"
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
include "wf1.mm"
include "wf.mm"
include "ccnv.mm"
include "wfun.mm"
include "wfn.mm"
include "crn.mm"
include "cuhgr.mm"
include "usgruhgr.mm"
include "subgruhgrfun.mm"
include "sylan.mm"
include "ancoms.mm"
include "funfn.mm"
include "sylib.mm"
include "adantl.mm"
include "wral.mm"
include "cumgr.mm"
include "simplrl.mm"
include "usgrumgr.mm"
include "adantr.mm"
include "simpr.mm"
include "subumgredg2.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "fnfvrnss.mm"
include "syl2anc.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "simp2.mm"
include "usgrfs.mm"
include "df-f1.mm"
include "ffun.mm"
include "anim1i.mm"
include "sylbi.mm"
include "syl.mm"
include "anim12ci.mm"
include "df-3an.mm"
include "sylibr.mm"
include "f1ssf1.mm"
include "wb.mm"
include "cvv.mm"
include "subgrv.mm"
include "isusgrs.mm"
include "mpbird.mm"
include "ex.mm"
include "anabsi8.mm"

theorem subusgr
  let cS: class S
  let cG: class G
  let vx: setvar x
  let ve: setvar e
  let vy: setvar y


  assert |- ( ( G e. USGraph /\ S SubGraph G ) -> S e. USGraph )

  proof
    cG
    cusgr
    wcel
    #
    cS
    cG
    csubgr
    wbr
    #
    cS
    cusgr
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
    #
    cS
    ciedg
    cfv
    #
    cG
    ciedg
    cfv
    #
    wss
    #
    cS
    cedg
    cfv
    #
    @3
    cpw
    #
    wss
    #
    w3a
    #
    @1
    @0
    wa
    #
    @2
    wi
    @4
    @7
    cS
    @9
    cG
    @6
    @3
    @3
    eqid
    #
    @4
    eqid
    #
    @6
    eqid
    #
    @7
    eqid
    #
    @9
    eqid
    subgrprop2
    @12
    @13
    @2
    @12
    @13
    wa
    #
    @2
    @6
    cdm
    #
    ve
    cv
    chash
    cfv
    c2
    wceq
    ve
    @10
    crab
    #
    @6
    wf1
    #
    @18
    @19
    @20
    @6
    wf
    #
    @6
    ccnv
    wfun
    #
    @21
    @18
    @6
    @19
    wfn
    #
    @6
    crn
    @20
    wss
    #
    @22
    @13
    @24
    @12
    @13
    @6
    wfun
    #
    @24
    @0
    @1
    @26
    @0
    cG
    cuhgr
    wcel
    @1
    @26
    cG
    usgruhgr
    cS
    cG
    subgruhgrfun
    sylan
    ancoms
    @6
    funfn
    sylib
    adantl
    #
    @18
    @24
    vx
    cv
    #
    @6
    cfv
    @20
    wcel
    #
    vx
    @19
    wral
    @25
    @27
    @18
    @29
    vx
    @19
    @18
    @28
    @19
    wcel
    #
    wa
    @1
    cG
    cumgr
    wcel
    #
    @30
    @29
    @12
    @1
    @0
    @30
    simplrl
    @18
    @31
    @30
    @13
    @31
    @12
    @0
    @31
    @1
    cG
    usgrumgr
    adantl
    adantl
    adantr
    @18
    @30
    simpr
    cS
    ve
    cG
    @6
    @3
    @28
    @14
    @16
    subumgredg2
    syl3anc
    ralrimiva
    vx
    @19
    @20
    @6
    fnfvrnss
    syl2anc
    @19
    @20
    @6
    df-f
    sylanbrc
    @18
    @7
    wfun
    #
    @7
    ccnv
    wfun
    #
    @8
    w3a
    #
    @23
    @18
    @32
    @33
    wa
    #
    @8
    wa
    @34
    @12
    @8
    @13
    @35
    @5
    @8
    @11
    simp2
    @0
    @35
    @1
    @0
    @7
    cdm
    #
    vy
    cv
    chash
    cfv
    c2
    wceq
    vy
    @4
    cpw
    crab
    #
    @7
    wf1
    #
    @35
    vy
    @7
    cG
    @4
    @15
    @17
    usgrfs
    @38
    @36
    @37
    @7
    wf
    #
    @33
    wa
    @35
    @36
    @37
    @7
    df-f1
    @39
    @32
    @33
    @36
    @37
    @7
    ffun
    anim1i
    sylbi
    syl
    adantl
    anim12ci
    @32
    @33
    @8
    df-3an
    sylibr
    @7
    @6
    f1ssf1
    syl
    @19
    @20
    @6
    df-f1
    sylanbrc
    @13
    @2
    @21
    wb
    #
    @12
    @1
    @40
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
    @40
    cS
    cG
    subgrv
    @41
    @40
    @42
    ve
    cvv
    @6
    cS
    @3
    @14
    @16
    isusgrs
    adantr
    syl
    adantr
    adantl
    mpbird
    ex
    syl
    anabsi8
end
