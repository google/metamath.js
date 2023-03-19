include "cupgr.mm"
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
include "cle.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wfun.mm"
include "cuhgr.mm"
include "upgruhgr.mm"
include "subgruhgrfun.mm"
include "sylan.mm"
include "ancoms.mm"
include "funfn.mm"
include "sylib.mm"
include "adantl.mm"
include "wral.mm"
include "anim2i.mm"
include "ancomd.mm"
include "anim1i.mm"
include "simplld.mm"
include "simpl.mm"
include "adantr.mm"
include "simpr.mm"
include "subgruhgredgd.mm"
include "wceq.mm"
include "uhgrfun.mm"
include "syl.mm"
include "ad2antll.mm"
include "simpll2.mm"
include "funssfv.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "subgreldmiedg.mm"
include "ex.mm"
include "upgrle.mm"
include "expcom.mm"
include "syld.mm"
include "imp.mm"
include "eqbrtrd.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ralrimiva.mm"
include "fnfvrnss.mm"
include "syl2anc.mm"
include "df-f.mm"
include "wb.mm"
include "cvv.mm"
include "subgrv.mm"
include "isupgr.mm"
include "mpbird.mm"
include "anabsi8.mm"

theorem subupgr
  let cS: class S
  let cG: class G
  let vx: setvar x
  let ve: setvar e


  assert |- ( ( G e. UPGraph /\ S SubGraph G ) -> S e. UPGraph )

  proof
    cG
    cupgr
    wcel
    #
    cS
    cG
    csubgr
    wbr
    #
    cS
    cupgr
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
    #
    chash
    cfv
    #
    c2
    cle
    wbr
    #
    ve
    @10
    c0
    csn
    cdif
    #
    crab
    #
    @6
    wf
    #
    @18
    @6
    @19
    wfn
    #
    @6
    crn
    @24
    wss
    #
    @25
    @13
    @26
    @12
    @13
    @6
    wfun
    #
    @26
    @0
    @1
    @28
    @0
    cG
    cuhgr
    wcel
    #
    @1
    @28
    cG
    upgruhgr
    #
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
    @26
    vx
    cv
    #
    @6
    cfv
    #
    @24
    wcel
    #
    vx
    @19
    wral
    @27
    @31
    @18
    @34
    vx
    @19
    @18
    @32
    @19
    wcel
    #
    wa
    #
    @33
    @23
    wcel
    @33
    chash
    cfv
    #
    c2
    cle
    wbr
    #
    @34
    @36
    cS
    cG
    @6
    @3
    @32
    @14
    @16
    @36
    @29
    @1
    @35
    @18
    @29
    @1
    wa
    @35
    @18
    @1
    @29
    @13
    @1
    @29
    wa
    @12
    @0
    @29
    @1
    @30
    anim2i
    adantl
    ancomd
    anim1i
    simplld
    @18
    @1
    @35
    @13
    @1
    @12
    @1
    @0
    simpl
    adantl
    adantr
    @18
    @35
    simpr
    #
    subgruhgredgd
    @36
    @37
    @32
    @7
    cfv
    #
    chash
    cfv
    #
    c2
    cle
    @36
    @33
    @40
    chash
    @36
    @40
    @33
    @36
    @7
    wfun
    #
    @8
    @35
    @40
    @33
    wceq
    @18
    @42
    @35
    @0
    @42
    @12
    @1
    @0
    @29
    @42
    @30
    @7
    cG
    @17
    uhgrfun
    syl
    #
    ad2antll
    adantr
    @5
    @8
    @11
    @13
    @35
    simpll2
    @39
    @32
    @7
    @6
    funssfv
    syl3anc
    eqcomd
    fveq2d
    @18
    @35
    @41
    c2
    cle
    wbr
    #
    @18
    @35
    @32
    @7
    cdm
    #
    wcel
    #
    @44
    @13
    @35
    @46
    wi
    #
    @12
    @1
    @47
    @0
    @1
    @35
    @46
    cS
    cG
    @32
    subgreldmiedg
    ex
    adantr
    adantl
    @0
    @46
    @44
    wi
    @12
    @1
    @46
    @0
    @44
    @46
    @0
    wa
    @0
    @7
    @45
    wfn
    #
    @46
    @44
    @46
    @0
    simpr
    @0
    @48
    @46
    @0
    @42
    @48
    @43
    @7
    funfn
    sylib
    adantl
    @46
    @0
    simpl
    @45
    @7
    @32
    cG
    @4
    @15
    @17
    upgrle
    syl3anc
    expcom
    ad2antll
    syld
    imp
    eqbrtrd
    @22
    @38
    ve
    @33
    @23
    @20
    @33
    wceq
    @21
    @37
    c2
    cle
    @20
    @33
    chash
    fveq2
    breq1d
    elrab
    sylanbrc
    ralrimiva
    vx
    @19
    @24
    @6
    fnfvrnss
    syl2anc
    @19
    @24
    @6
    df-f
    sylanbrc
    @13
    @2
    @25
    wb
    #
    @12
    @1
    @49
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
    @49
    cS
    cG
    subgrv
    @50
    @49
    @51
    ve
    cvv
    @6
    cS
    @3
    @14
    @16
    isupgr
    adantr
    syl
    adantr
    adantl
    mpbird
    ex
    syl
    anabsi8
end
