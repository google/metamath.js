include "csqrt.mm"
include "cres.mm"
include "cc.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "wtru.mm"
include "cv.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "ccxp.mm"
include "cmpt.mm"
include "cfv.mm"
include "wf.mm"
include "sqrtf.mm"
include "a1i.mm"
include "feqmptd.mm"
include "reseq1d.mm"
include "wss.mm"
include "wceq.mm"
include "cmnf.mm"
include "cc0.mm"
include "cioc.mm"
include "cdif.mm"
include "difss.mm"
include "eqsstri.mm"
include "resmpt.mm"
include "mp1i.mm"
include "wa.mm"
include "sseli.mm"
include "adantl.mm"
include "cxpsqrt.mm"
include "syl.mm"
include "eqcomd.mm"
include "mpteq2dva.mm"
include "3eqtrd.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "ccn.mm"
include "ctopon.mm"
include "eqid.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "sylancl.mm"
include "cnmptid.mm"
include "ax-1cn.mm"
include "halfcl.mm"
include "cnmptc.mm"
include "cmpt2.mm"
include "ctx.mm"
include "cxpcn.mm"
include "oveq12.mm"
include "cnmpt12.mm"
include "ssid.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "mp2an.mm"
include "syl6eleqr.mm"
include "eqeltrd.mm"
include "trud.mm"

theorem sqrtcn
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume sqrcn.d: |- D = ( CC \ ( -oo (,] 0 ) )


  assert |- ( sqrt |` D ) e. ( D -cn-> CC )

  proof
    csqrt
    cD
    cres
    #
    cD
    cc
    ccncf
    co
    #
    wcel
    wtru
    @0
    vx
    cD
    vx
    cv
    #
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
    @1
    wtru
    @0
    vx
    cc
    @2
    csqrt
    cfv
    #
    cmpt
    #
    cD
    cres
    #
    vx
    cD
    @6
    cmpt
    #
    @5
    wtru
    csqrt
    @7
    cD
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
    cD
    cc
    wss
    #
    @8
    @9
    wceq
    wtru
    cD
    cc
    cmnf
    cc0
    cioc
    co
    #
    cdif
    cc
    sqrcn.d
    cc
    @11
    difss
    eqsstri
    #
    vx
    cc
    cD
    @6
    resmpt
    mp1i
    wtru
    vx
    cD
    @6
    @4
    wtru
    @2
    cD
    wcel
    #
    wa
    #
    @4
    @6
    @14
    @2
    cc
    wcel
    #
    @4
    @6
    wceq
    @13
    @15
    wtru
    cD
    cc
    @2
    @12
    sseli
    adantl
    @2
    cxpsqrt
    syl
    eqcomd
    mpteq2dva
    3eqtrd
    wtru
    @5
    ccnfld
    ctopn
    cfv
    #
    cD
    crest
    co
    #
    @16
    ccn
    co
    #
    @1
    wtru
    vx
    vy
    vz
    @2
    @3
    vy
    cv
    #
    vz
    cv
    #
    ccxp
    co
    #
    @4
    @17
    @17
    @16
    @16
    cD
    cD
    cc
    wtru
    @16
    cc
    ctopon
    cfv
    #
    wcel
    #
    @10
    @17
    cD
    ctopon
    cfv
    wcel
    @23
    wtru
    @16
    @16
    eqid
    #
    cnfldtopon
    #
    a1i
    #
    @12
    cD
    @16
    cc
    resttopon
    sylancl
    #
    wtru
    vx
    @17
    cD
    @27
    cnmptid
    wtru
    vx
    @3
    @17
    @16
    cD
    cc
    @27
    @26
    c1
    cc
    wcel
    @3
    cc
    wcel
    wtru
    ax-1cn
    c1
    halfcl
    mp1i
    cnmptc
    @27
    @26
    vy
    vz
    cD
    cc
    @21
    cmpt2
    @17
    @16
    ctx
    co
    @16
    ccn
    co
    wcel
    wtru
    vy
    vz
    cD
    @16
    @17
    sqrcn.d
    @24
    @17
    eqid
    #
    cxpcn
    a1i
    @19
    @2
    @20
    @3
    ccxp
    oveq12
    cnmpt12
    @10
    cc
    cc
    wss
    @1
    @18
    wceq
    @12
    cc
    ssid
    cD
    cc
    @16
    @17
    @16
    @24
    @28
    @16
    cc
    crest
    co
    #
    @16
    @23
    @29
    @16
    wceq
    @25
    @16
    @22
    cc
    cc
    @16
    @25
    toponunii
    restid
    ax-mp
    eqcomi
    cncfcn
    mp2an
    syl6eleqr
    eqeltrd
    trud
end
