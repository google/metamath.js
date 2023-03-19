include "ccos.mm"
include "cc.mm"
include "ci.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "cneg.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "cmpt.mm"
include "ccncf.mm"
include "df-cos.mm"
include "wcel.mm"
include "wtru.mm"
include "ccom.mm"
include "wf.mm"
include "wral.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "ctx.mm"
include "ccn.mm"
include "addcn.mm"
include "a1i.mm"
include "efcn.mm"
include "ax-icn.mm"
include "mulc1cncf.mm"
include "mp1i.mm"
include "cncfmpt1f.mm"
include "negicn.mm"
include "cncfmpt2f.mm"
include "cncff.mm"
include "syl.mm"
include "fmpt.mm"
include "sylibr.mm"
include "eqidd.mm"
include "oveq1.mm"
include "fmptcof.mm"
include "cc0.mm"
include "wne.mm"
include "2cn.mm"
include "2ne0.mm"
include "divccncf.mm"
include "mp2an.mm"
include "cncfco.mm"
include "eqeltrrd.mm"
include "trud.mm"
include "eqeltri.mm"

theorem coscn
  let vx: setvar x
  let vy: setvar y


  assert |- cos e. ( CC -cn-> CC )

  proof
    ccos
    vx
    cc
    ci
    vx
    cv
    #
    cmul
    co
    #
    ce
    cfv
    #
    ci
    cneg
    #
    @0
    cmul
    co
    #
    ce
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cmpt
    #
    cc
    cc
    ccncf
    co
    #
    vx
    df-cos
    @8
    @9
    wcel
    wtru
    vy
    cc
    vy
    cv
    #
    c2
    cdiv
    co
    #
    cmpt
    #
    vx
    cc
    @6
    cmpt
    #
    ccom
    @8
    @9
    wtru
    vx
    vy
    cc
    cc
    @6
    @11
    @7
    @13
    @12
    wtru
    cc
    cc
    @13
    wf
    #
    @6
    cc
    wcel
    vx
    cc
    wral
    wtru
    @13
    @9
    wcel
    @14
    wtru
    vx
    @2
    @5
    caddc
    ccnfld
    ctopn
    cfv
    #
    cc
    @15
    eqid
    #
    caddc
    @15
    @15
    ctx
    co
    @15
    ccn
    co
    wcel
    wtru
    @15
    @16
    addcn
    a1i
    wtru
    vx
    @1
    ce
    cc
    ce
    @9
    wcel
    wtru
    efcn
    a1i
    #
    ci
    cc
    wcel
    vx
    cc
    @1
    cmpt
    #
    @9
    wcel
    wtru
    ax-icn
    vx
    ci
    @18
    @18
    eqid
    mulc1cncf
    mp1i
    cncfmpt1f
    wtru
    vx
    @4
    ce
    cc
    @17
    @3
    cc
    wcel
    vx
    cc
    @4
    cmpt
    #
    @9
    wcel
    wtru
    negicn
    vx
    @3
    @19
    @19
    eqid
    mulc1cncf
    mp1i
    cncfmpt1f
    cncfmpt2f
    #
    cc
    cc
    @13
    cncff
    syl
    vx
    cc
    cc
    @6
    @13
    @13
    eqid
    fmpt
    sylibr
    wtru
    @13
    eqidd
    wtru
    @12
    eqidd
    @10
    @6
    c2
    cdiv
    oveq1
    fmptcof
    wtru
    cc
    cc
    cc
    @13
    @12
    @20
    @12
    @9
    wcel
    #
    wtru
    c2
    cc
    wcel
    c2
    cc0
    wne
    @21
    2cn
    2ne0
    vy
    c2
    @12
    @12
    eqid
    divccncf
    mp2an
    a1i
    cncfco
    eqeltrrd
    trud
    eqeltri
end
