include "cva.mm"
include "cgr.mm"
include "wcel.mm"
include "cxp.mm"
include "cres.mm"
include "wss.mm"
include "cablo.mm"
include "hilablo.mm"
include "ablogrpo.mm"
include "ax-mp.mm"
include "cgi.mm"
include "cfv.mm"
include "cv.mm"
include "cgn.mm"
include "csh.mm"
include "elexi.mm"
include "wf.mm"
include "wfn.mm"
include "co.mm"
include "wral.mm"
include "crn.mm"
include "wfo.mm"
include "eqid.mm"
include "grpofo.mm"
include "fof.mm"
include "mp2b.mm"
include "chil.mm"
include "shssii.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "df-hba.mm"
include "hhva.mm"
include "bafval.mm"
include "sseqtri.mm"
include "xpss12.mm"
include "mp2an.mm"
include "fssres.mm"
include "ffn.mm"
include "wa.mm"
include "ovres.mm"
include "shaddcl.mm"
include "mp3an1.mm"
include "eqeltrd.mm"
include "rgen2a.mm"
include "ffnov.mm"
include "mpbir2an.mm"
include "w3a.mm"
include "wceq.mm"
include "oveq1d.mm"
include "3adant3.mm"
include "stoic3.mm"
include "oveq2d.mm"
include "3adant1.mm"
include "fovcl.mm"
include "sylan2.mm"
include "3impb.mm"
include "sseli.mm"
include "grpoass.mm"
include "mpan.mm"
include "syl3an.mm"
include "3eqtr4d.mm"
include "c0v.mm"
include "hilid.mm"
include "sh0.mm"
include "eqeltri.mm"
include "grpolid.mm"
include "sylancr.mm"
include "eqtrd.mm"
include "c2nd.mm"
include "c1.mm"
include "cneg.mm"
include "csn.mm"
include "cvv.mm"
include "ccnv.mm"
include "ccom.mm"
include "cnv.mm"
include "hhnv.mm"
include "hhsm.mm"
include "nvinvfval.mm"
include "eqcomi.mm"
include "fveq1i.mm"
include "cc.mm"
include "ax-hfvmul.mm"
include "neg1cn.mm"
include "curry1val.mm"
include "shmulcl.mm"
include "mp3an12.mm"
include "syl5eqel.mm"
include "mpancom.mm"
include "grpolinv.mm"
include "isgrpoi.mm"
include "resss.mm"
include "3pm3.2i.mm"

theorem hhssabloilem
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume hhssabl.1: |- H e. SH


  assert |- ( +h e. GrpOp /\ ( +h |` ( H X. H ) ) e. GrpOp /\ ( +h |` ( H X. H ) ) C_ +h )

  proof
    cva
    cgr
    wcel
    #
    cva
    cH
    cH
    cxp
    #
    cres
    #
    cgr
    wcel
    @2
    cva
    wss
    cva
    cablo
    wcel
    @0
    hilablo
    cva
    ablogrpo
    ax-mp
    #
    vx
    vy
    vz
    cva
    cgi
    cfv
    #
    @2
    vx
    cv
    #
    cva
    cgn
    cfv
    #
    cfv
    #
    cH
    cH
    csh
    hhssabl.1
    elexi
    @1
    cH
    @2
    wf
    @2
    @1
    wfn
    #
    @5
    vy
    cv
    #
    @2
    co
    #
    cH
    wcel
    #
    vy
    cH
    wral
    vx
    cH
    wral
    @1
    cva
    crn
    #
    @2
    wf
    #
    @8
    @12
    @12
    cxp
    #
    @12
    cva
    wf
    #
    @1
    @14
    wss
    #
    @13
    @0
    @14
    @12
    cva
    wfo
    @15
    @3
    cva
    @12
    @12
    eqid
    #
    grpofo
    @14
    @12
    cva
    fof
    mp2b
    cH
    @12
    wss
    #
    @18
    @16
    cH
    chil
    @12
    cH
    hhssabl.1
    shssii
    cva
    csm
    cop
    cno
    cop
    #
    cva
    chil
    df-hba
    @19
    @19
    eqid
    #
    hhva
    #
    bafval
    sseqtri
    #
    @22
    cH
    @12
    cH
    @12
    xpss12
    mp2an
    @14
    @12
    @1
    cva
    fssres
    mp2an
    @1
    @12
    @2
    ffn
    ax-mp
    @11
    vx
    vy
    cH
    @5
    cH
    wcel
    #
    @9
    cH
    wcel
    #
    wa
    #
    @10
    @5
    @9
    cva
    co
    #
    cH
    @5
    @9
    cH
    cH
    cva
    ovres
    #
    cH
    csh
    wcel
    #
    @23
    @24
    @26
    cH
    wcel
    hhssabl.1
    @5
    @9
    cH
    shaddcl
    mp3an1
    eqeltrd
    #
    rgen2a
    vx
    vy
    cH
    cH
    cH
    @2
    ffnov
    mpbir2an
    #
    @23
    @24
    vz
    cv
    #
    cH
    wcel
    #
    w3a
    #
    @10
    @31
    cva
    co
    #
    @26
    @31
    cva
    co
    #
    @10
    @31
    @2
    co
    #
    @5
    @9
    @31
    @2
    co
    #
    @2
    co
    #
    @23
    @24
    @34
    @35
    wceq
    @32
    @25
    @10
    @26
    @31
    cva
    @27
    oveq1d
    3adant3
    @23
    @24
    @11
    @32
    @36
    @34
    wceq
    @29
    @10
    @31
    cH
    cH
    cva
    ovres
    stoic3
    @33
    @5
    @37
    cva
    co
    #
    @5
    @9
    @31
    cva
    co
    #
    cva
    co
    #
    @38
    @35
    @24
    @32
    @39
    @41
    wceq
    @23
    @24
    @32
    wa
    #
    @37
    @40
    @5
    cva
    @9
    @31
    cH
    cH
    cva
    ovres
    oveq2d
    3adant1
    @23
    @24
    @32
    @38
    @39
    wceq
    #
    @42
    @23
    @37
    cH
    wcel
    @43
    @9
    @31
    cH
    cH
    cH
    @2
    @30
    fovcl
    @5
    @37
    cH
    cH
    cva
    ovres
    sylan2
    3impb
    @23
    @5
    @12
    wcel
    #
    @24
    @9
    @12
    wcel
    #
    @32
    @31
    @12
    wcel
    #
    @35
    @41
    wceq
    #
    cH
    @12
    @5
    @22
    sseli
    #
    cH
    @12
    @9
    @22
    sseli
    cH
    @12
    @31
    @22
    sseli
    @0
    @44
    @45
    @46
    w3a
    @47
    @3
    @5
    @9
    @31
    cva
    @12
    @17
    grpoass
    mpan
    syl3an
    3eqtr4d
    3eqtr4d
    @4
    c0v
    cH
    hilid
    @28
    c0v
    cH
    wcel
    hhssabl.1
    cH
    sh0
    ax-mp
    eqeltri
    #
    @23
    @4
    @5
    @2
    co
    #
    @4
    @5
    cva
    co
    #
    @5
    @4
    cH
    wcel
    @23
    @50
    @51
    wceq
    @49
    @4
    @5
    cH
    cH
    cva
    ovres
    mpan
    @23
    @0
    @44
    @51
    @5
    wceq
    @3
    @48
    @5
    @4
    cva
    @12
    @17
    @4
    eqid
    #
    grpolid
    sylancr
    eqtrd
    @23
    @7
    @5
    csm
    c2nd
    c1
    cneg
    #
    csn
    cvv
    cxp
    cres
    ccnv
    ccom
    #
    cfv
    #
    cH
    @5
    @6
    @54
    @54
    @6
    @19
    cnv
    wcel
    @54
    @6
    wceq
    @19
    @20
    hhnv
    csm
    @19
    cva
    @54
    @21
    @19
    @20
    hhsm
    @54
    eqid
    #
    nvinvfval
    ax-mp
    eqcomi
    fveq1i
    @23
    @55
    @53
    @5
    csm
    co
    #
    cH
    csm
    cc
    chil
    cxp
    #
    wfn
    #
    @53
    cc
    wcel
    #
    @55
    @57
    wceq
    @58
    chil
    csm
    wf
    @59
    ax-hfvmul
    @58
    chil
    csm
    ffn
    ax-mp
    neg1cn
    cc
    chil
    @53
    @5
    csm
    @54
    @56
    curry1val
    mp2an
    @28
    @60
    @23
    @57
    cH
    wcel
    hhssabl.1
    neg1cn
    @53
    @5
    cH
    shmulcl
    mp3an12
    syl5eqel
    syl5eqel
    #
    @23
    @7
    @5
    @2
    co
    #
    @7
    @5
    cva
    co
    #
    @4
    @7
    cH
    wcel
    @23
    @62
    @63
    wceq
    @61
    @7
    @5
    cH
    cH
    cva
    ovres
    mpancom
    @23
    @0
    @44
    @63
    @4
    wceq
    @3
    @48
    @5
    @4
    cva
    @6
    @12
    @17
    @52
    @6
    eqid
    grpolinv
    sylancr
    eqtrd
    isgrpoi
    cva
    @1
    resss
    3pm3.2i
end
