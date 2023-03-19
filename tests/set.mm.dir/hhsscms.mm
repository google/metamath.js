include "cmopn.mm"
include "cfv.mm"
include "eqid.mm"
include "chshii.mm"
include "hhssmet.mm"
include "cv.mm"
include "cca.mm"
include "wcel.mm"
include "cn.mm"
include "wf.mm"
include "wa.mm"
include "chli.mm"
include "clm.mm"
include "wbr.mm"
include "cdm.mm"
include "cno.mm"
include "cmv.mm"
include "ccom.mm"
include "ccau.mm"
include "chil.mm"
include "wrex.mm"
include "cmap.mm"
include "co.mm"
include "cxp.mm"
include "cres.mm"
include "simpl.mm"
include "hhssims2.mm"
include "fveq2i.mm"
include "syl6eleq.mm"
include "cxmt.mm"
include "wb.mm"
include "hilxmet.mm"
include "simpr.mm"
include "causs.mm"
include "sylancr.mm"
include "mpbird.mm"
include "wss.mm"
include "chssii.mm"
include "fss.mm"
include "sylancl.mm"
include "ax-hilex.mm"
include "nnex.mm"
include "elmap.mm"
include "sylibr.mm"
include "cva.mm"
include "csm.mm"
include "cop.mm"
include "hhims.mm"
include "hhcau.mm"
include "elin2.mm"
include "sylanbrc.mm"
include "ax-hcompl.mm"
include "vex.mm"
include "breldm.mm"
include "rexlimivw.mm"
include "3syl.mm"
include "wfun.mm"
include "hlimf.mm"
include "ffun.mm"
include "funfvbrb.mm"
include "mp2b.mm"
include "sylib.mm"
include "hhlm.mm"
include "resss.mm"
include "eqsstri.mm"
include "ssbri.mm"
include "syl.mm"
include "c1.mm"
include "cch.mm"
include "crest.mm"
include "wceq.mm"
include "metrest.mm"
include "mp2an.mm"
include "eqcomi.mm"
include "nnuz.mm"
include "a1i.mm"
include "ctop.mm"
include "mopntop.mm"
include "mp1i.mm"
include "fvex.mm"
include "chlimi.mm"
include "syl3anc.mm"
include "1zzd.mm"
include "lmss.mm"
include "mpbid.mm"
include "iscmet3i.mm"

theorem hhsscms
  let cD: class D
  let cH: class H
  let cW: class W
  let vf: setvar f
  let vx: setvar x
  assume hhssims2.1: |- W = <. <. ( +h |` ( H X. H ) ) , ( .h |` ( CC X. H ) ) >. , ( normh |` H ) >.
  assume hhssims2.3: |- D = ( IndMet ` W )
  assume hhsscms.3: |- H e. CH


  assert |- D e. ( CMet ` H )

  proof
    cD
    vf
    cD
    cmopn
    cfv
    #
    cH
    @0
    eqid
    #
    cD
    cH
    cW
    hhssims2.1
    hhssims2.3
    cH
    hhsscms.3
    chshii
    #
    hhssmet
    vf
    cv
    #
    cD
    cca
    cfv
    #
    wcel
    #
    cn
    cH
    @3
    wf
    #
    wa
    #
    @3
    @3
    chli
    cfv
    #
    @0
    clm
    cfv
    #
    wbr
    #
    @3
    @9
    cdm
    wcel
    @7
    @3
    @8
    cno
    cmv
    ccom
    #
    cmopn
    cfv
    #
    clm
    cfv
    #
    wbr
    #
    @10
    @7
    @3
    @8
    chli
    wbr
    #
    @14
    @7
    @3
    chli
    cdm
    #
    wcel
    #
    @15
    @7
    @3
    ccau
    wcel
    #
    @3
    vx
    cv
    #
    chli
    wbr
    #
    vx
    chil
    wrex
    @17
    @7
    @3
    @11
    cca
    cfv
    #
    wcel
    #
    @3
    chil
    cn
    cmap
    co
    #
    wcel
    #
    @18
    @7
    @22
    @3
    @11
    cH
    cH
    cxp
    cres
    #
    cca
    cfv
    #
    wcel
    #
    @7
    @3
    @4
    @26
    @5
    @6
    simpl
    cD
    @25
    cca
    cD
    cH
    cW
    hhssims2.1
    hhssims2.3
    @2
    hhssims2
    #
    fveq2i
    syl6eleq
    @7
    @11
    chil
    cxmt
    cfv
    wcel
    #
    @6
    @22
    @27
    wb
    @11
    @11
    eqid
    #
    hilxmet
    #
    @5
    @6
    simpr
    #
    @11
    @3
    chil
    cH
    causs
    sylancr
    mpbird
    @7
    cn
    chil
    @3
    wf
    #
    @24
    @7
    @6
    cH
    chil
    wss
    #
    @33
    @32
    cH
    hhsscms.3
    chssii
    #
    cn
    cH
    chil
    @3
    fss
    sylancl
    chil
    cn
    @3
    ax-hilex
    nnex
    elmap
    sylibr
    @3
    @21
    @23
    ccau
    @11
    cva
    csm
    cop
    cno
    cop
    #
    @36
    eqid
    #
    @11
    @36
    @37
    @30
    hhims
    #
    hhcau
    elin2
    sylanbrc
    vx
    @3
    ax-hcompl
    @20
    @17
    vx
    chil
    @3
    @19
    chli
    vf
    vex
    #
    vx
    vex
    breldm
    rexlimivw
    3syl
    @16
    chil
    chli
    wf
    chli
    wfun
    @17
    @15
    wb
    hlimf
    @16
    chil
    chli
    ffun
    @3
    chli
    funfvbrb
    mp2b
    sylib
    #
    chli
    @13
    @3
    @8
    chli
    @13
    @23
    cres
    @13
    @11
    @36
    @12
    @37
    @38
    @12
    eqid
    #
    hhlm
    @13
    @23
    resss
    eqsstri
    ssbri
    syl
    @7
    @8
    @3
    @12
    @0
    c1
    cch
    cH
    cn
    @12
    cH
    crest
    co
    #
    @0
    @29
    @34
    @42
    @0
    wceq
    @31
    @35
    @11
    cD
    @12
    @0
    chil
    cH
    @28
    @41
    @1
    metrest
    mp2an
    eqcomi
    nnuz
    cH
    cch
    wcel
    #
    @7
    hhsscms.3
    a1i
    #
    @29
    @12
    ctop
    wcel
    @7
    @31
    @11
    @12
    chil
    @41
    mopntop
    mp1i
    @7
    @43
    @6
    @15
    @8
    cH
    wcel
    @44
    @32
    @40
    @8
    @3
    cH
    @3
    chli
    fvex
    #
    chlimi
    syl3anc
    @7
    1zzd
    @32
    lmss
    mpbid
    @3
    @8
    @9
    @39
    @45
    breldm
    syl
    iscmet3i
end
