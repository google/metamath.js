include "csqrt.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cres.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cr.mm"
include "ccncf.mm"
include "wceq.mm"
include "wtru.mm"
include "cc.mm"
include "wf.mm"
include "sqrtf.mm"
include "a1i.mm"
include "feqmptd.mm"
include "reseq1d.mm"
include "wss.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "elrege0.mm"
include "simplbi.mm"
include "recnd.mm"
include "ssriv.mm"
include "resmpt.mm"
include "mp1i.mm"
include "eqtrd.mm"
include "trud.mm"
include "eqid.mm"
include "wa.mm"
include "resqrtcl.mm"
include "sylbi.mm"
include "fmpti.mm"
include "wb.mm"
include "ax-resscn.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "ccxp.mm"
include "cxpsqrt.mm"
include "syl.mm"
include "mpteq2ia.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "ccn.mm"
include "cre.mm"
include "ccnv.mm"
include "crp.mm"
include "cima.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "sylancl.mm"
include "cnmptid.mm"
include "cdm.mm"
include "cnvimass.mm"
include "ref.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "halfcn.mm"
include "1rp.mm"
include "rphalfcl.mm"
include "ax-mp.mm"
include "rpre.mm"
include "rere.mm"
include "mp2b.mm"
include "eqeltri.mm"
include "wfn.mm"
include "ffn.mm"
include "elpreima.mm"
include "mpbir2an.mm"
include "cnmptc.mm"
include "cmpt2.mm"
include "ctx.mm"
include "cxpcn3.mm"
include "oveq12.mm"
include "cnmpt12.mm"
include "ssid.mm"
include "toponunii.mm"
include "restid.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "mp2an.mm"
include "syl6eleqr.mm"
include "syl5eqelr.mm"
include "cncffvrn.mm"
include "mpbir.mm"

theorem resqrtcn
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D


  assert |- ( sqrt |` ( 0 [,) +oo ) ) e. ( ( 0 [,) +oo ) -cn-> RR )

  proof
    csqrt
    cc0
    cpnf
    cico
    co
    #
    cres
    #
    vx
    @0
    vx
    cv
    #
    csqrt
    cfv
    #
    cmpt
    #
    @0
    cr
    ccncf
    co
    #
    @1
    @4
    wceq
    wtru
    @1
    vx
    cc
    @3
    cmpt
    #
    @0
    cres
    #
    @4
    wtru
    csqrt
    @6
    @0
    wtru
    vx
    cc
    cc
    csqrt
    cc
    cc
    csqrt
    wf
    wtru
    sqrtf
    a1i
    feqmptd
    reseq1d
    @0
    cc
    wss
    #
    @7
    @4
    wceq
    wtru
    vx
    @0
    cc
    @2
    @0
    wcel
    #
    @2
    @9
    @2
    cr
    wcel
    #
    cc0
    @2
    cle
    wbr
    #
    @2
    elrege0
    #
    simplbi
    recnd
    #
    ssriv
    #
    vx
    cc
    @0
    @3
    resmpt
    mp1i
    eqtrd
    trud
    @4
    @5
    wcel
    #
    @0
    cr
    @4
    wf
    #
    vx
    @0
    cr
    @3
    @4
    @4
    eqid
    @9
    @10
    @11
    wa
    @3
    cr
    wcel
    @12
    @2
    resqrtcl
    sylbi
    fmpti
    cr
    cc
    wss
    @4
    @0
    cc
    ccncf
    co
    #
    wcel
    #
    @15
    @16
    wb
    ax-resscn
    @18
    wtru
    @4
    vx
    @0
    @2
    c1
    c2
    cdiv
    co
    #
    ccxp
    co
    #
    cmpt
    #
    @17
    vx
    @0
    @20
    @3
    @9
    @2
    cc
    wcel
    @20
    @3
    wceq
    @13
    @2
    cxpsqrt
    syl
    mpteq2ia
    wtru
    @21
    ccnfld
    ctopn
    cfv
    #
    @0
    crest
    co
    #
    @22
    ccn
    co
    #
    @17
    wtru
    vx
    vy
    vz
    @2
    @19
    vy
    cv
    #
    vz
    cv
    #
    ccxp
    co
    #
    @20
    @23
    @23
    @22
    cre
    ccnv
    crp
    cima
    #
    crest
    co
    #
    @22
    @0
    @0
    @28
    wtru
    @22
    cc
    ctopon
    cfv
    #
    wcel
    #
    @8
    @23
    @0
    ctopon
    cfv
    wcel
    @31
    wtru
    @22
    @22
    eqid
    #
    cnfldtopon
    #
    a1i
    #
    @14
    @0
    @22
    cc
    resttopon
    sylancl
    #
    wtru
    vx
    @23
    @0
    @35
    cnmptid
    wtru
    vx
    @19
    @23
    @29
    @0
    @28
    @35
    wtru
    @31
    @28
    cc
    wss
    @29
    @28
    ctopon
    cfv
    wcel
    @34
    @28
    cre
    cdm
    cc
    cre
    crp
    cnvimass
    cc
    cr
    cre
    ref
    fdmi
    sseqtri
    @28
    @22
    cc
    resttopon
    sylancl
    #
    @19
    @28
    wcel
    #
    wtru
    @37
    @19
    cc
    wcel
    #
    @19
    cre
    cfv
    #
    crp
    wcel
    #
    halfcn
    @39
    @19
    crp
    @19
    crp
    wcel
    #
    @19
    cr
    wcel
    @39
    @19
    wceq
    c1
    crp
    wcel
    @41
    1rp
    c1
    rphalfcl
    ax-mp
    #
    @19
    rpre
    @19
    rere
    mp2b
    @42
    eqeltri
    cc
    cr
    cre
    wf
    cre
    cc
    wfn
    @37
    @38
    @40
    wa
    wb
    ref
    cc
    cr
    cre
    ffn
    cc
    @19
    crp
    cre
    elpreima
    mp2b
    mpbir2an
    a1i
    cnmptc
    @35
    @36
    vy
    vz
    @0
    @28
    @27
    cmpt2
    @23
    @29
    ctx
    co
    @22
    ccn
    co
    wcel
    wtru
    vy
    vz
    @28
    @22
    @23
    @29
    @28
    eqid
    @32
    @23
    eqid
    #
    @29
    eqid
    cxpcn3
    a1i
    @25
    @2
    @26
    @19
    ccxp
    oveq12
    cnmpt12
    @8
    cc
    cc
    wss
    @17
    @24
    wceq
    @14
    cc
    ssid
    @0
    cc
    @22
    @23
    @22
    @32
    @43
    @22
    cc
    crest
    co
    #
    @22
    @31
    @44
    @22
    wceq
    @33
    @22
    @30
    cc
    cc
    @22
    @33
    toponunii
    restid
    ax-mp
    eqcomi
    cncfcn
    mp2an
    syl6eleqr
    syl5eqelr
    trud
    @0
    cc
    cr
    @4
    cncffvrn
    mp2an
    mpbir
    eqeltri
end
