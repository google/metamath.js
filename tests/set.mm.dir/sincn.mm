include "csin.mm"
include "cc.mm"
include "ci.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "cneg.mm"
include "cmin.mm"
include "c2.mm"
include "cdiv.mm"
include "cmpt.mm"
include "ccncf.mm"
include "df-sin.mm"
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
include "subcn.mm"
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
include "2mulicn.mm"
include "2muline0.mm"
include "divccncf.mm"
include "mp2an.mm"
include "cncfco.mm"
include "eqeltrrd.mm"
include "trud.mm"
include "eqeltri.mm"

theorem sincn
  let vx: setvar x
  let vy: setvar y


  assert |- sin e. ( CC -cn-> CC )

  proof
    csin
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
    cmin
    co
    #
    c2
    ci
    cmul
    co
    #
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
    df-sin
    @9
    @10
    wcel
    wtru
    vy
    cc
    vy
    cv
    #
    @7
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
    @9
    @10
    wtru
    vx
    vy
    cc
    cc
    @6
    @12
    @8
    @14
    @13
    wtru
    cc
    cc
    @14
    wf
    #
    @6
    cc
    wcel
    vx
    cc
    wral
    wtru
    @14
    @10
    wcel
    @15
    wtru
    vx
    @2
    @5
    cmin
    ccnfld
    ctopn
    cfv
    #
    cc
    @16
    eqid
    #
    cmin
    @16
    @16
    ctx
    co
    @16
    ccn
    co
    wcel
    wtru
    @16
    @17
    subcn
    a1i
    wtru
    vx
    @1
    ce
    cc
    ce
    @10
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
    @10
    wcel
    wtru
    ax-icn
    vx
    ci
    @19
    @19
    eqid
    mulc1cncf
    mp1i
    cncfmpt1f
    wtru
    vx
    @4
    ce
    cc
    @18
    @3
    cc
    wcel
    vx
    cc
    @4
    cmpt
    #
    @10
    wcel
    wtru
    negicn
    vx
    @3
    @20
    @20
    eqid
    mulc1cncf
    mp1i
    cncfmpt1f
    cncfmpt2f
    #
    cc
    cc
    @14
    cncff
    syl
    vx
    cc
    cc
    @6
    @14
    @14
    eqid
    fmpt
    sylibr
    wtru
    @14
    eqidd
    wtru
    @13
    eqidd
    @11
    @6
    @7
    cdiv
    oveq1
    fmptcof
    wtru
    cc
    cc
    cc
    @14
    @13
    @21
    @13
    @10
    wcel
    #
    wtru
    @7
    cc
    wcel
    @7
    cc0
    wne
    @22
    2mulicn
    2muline0
    vy
    @7
    @13
    @13
    eqid
    divccncf
    mp2an
    a1i
    cncfco
    eqeltrrd
    trud
    eqeltri
end
