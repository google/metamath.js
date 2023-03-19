include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "ccnfld.mm"
include "cgsu.mm"
include "cmpt.mm"
include "c0g.mm"
include "csupp.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cmnf.mm"
include "csn.mm"
include "cun.mm"
include "eqid.mm"
include "mdegval.mm"
include "c0.mm"
include "wceq.mm"
include "supeq1.mm"
include "eleq1d.mm"
include "wne.mm"
include "wa.mm"
include "wss.mm"
include "crn.mm"
include "imassrn.mm"
include "cvv.mm"
include "wf.mm"
include "mplrcl.mm"
include "tdeglem1.mm"
include "frn.mm"
include "3syl.mm"
include "syl5ss.mm"
include "adantr.mm"
include "ssun1.mm"
include "syl6ss.mm"
include "wfun.mm"
include "ffun.mm"
include "id.mm"
include "cmpl.mm"
include "reldmmpl.mm"
include "elbasov.mm"
include "simprd.mm"
include "mplelsfi.mm"
include "fsuppimpd.mm"
include "imafi.mm"
include "syl2anc.mm"
include "simpr.mm"
include "cr.mm"
include "nn0ssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "wor.mm"
include "w3a.mm"
include "xrltso.mm"
include "fisupcl.mm"
include "mpan.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "xrsup0.mm"
include "ssun2.mm"
include "mnfxr.mm"
include "elexi.mm"
include "snid.mm"
include "sselii.mm"
include "eqeltri.mm"
include "a1i.mm"
include "pm2.61ne.mm"
include "eqeltrd.mm"

theorem mdegcl
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cF: class F
  let cI: class I
  let va: setvar a
  let vb: setvar b
  assume mdegcl.d: |- D = ( I mDeg R )
  assume mdegcl.p: |- P = ( I mPoly R )
  assume mdegcl.b: |- B = ( Base ` P )


  assert |- ( F e. B -> ( D ` F ) e. ( NN0 u. { -oo } ) )

  proof
    cF
    cB
    wcel
    #
    cF
    cD
    cfv
    vb
    va
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    va
    cn0
    cI
    cmap
    co
    crab
    #
    ccnfld
    vb
    cv
    cgsu
    co
    cmpt
    #
    cF
    cR
    c0g
    cfv
    #
    csupp
    co
    #
    cima
    #
    cxr
    clt
    csup
    #
    cn0
    cmnf
    csn
    #
    cun
    #
    @1
    cB
    cD
    cP
    cR
    vb
    va
    cF
    @2
    cI
    @3
    mdegcl.d
    mdegcl.p
    mdegcl.b
    @3
    eqid
    #
    @1
    eqid
    #
    @2
    eqid
    #
    mdegval
    @0
    @6
    @8
    wcel
    c0
    cxr
    clt
    csup
    #
    @8
    wcel
    #
    @5
    c0
    @5
    c0
    wceq
    @6
    @12
    @8
    cxr
    @5
    c0
    clt
    supeq1
    eleq1d
    @0
    @5
    c0
    wne
    #
    wa
    #
    @5
    @8
    @6
    @15
    @5
    cn0
    @8
    @0
    @5
    cn0
    wss
    @14
    @0
    @5
    @2
    crn
    #
    cn0
    @2
    @4
    imassrn
    @0
    cI
    cvv
    wcel
    #
    @1
    cn0
    @2
    wf
    #
    @16
    cn0
    wss
    cB
    cP
    cR
    cI
    cF
    mdegcl.p
    mdegcl.b
    mplrcl
    #
    @1
    vb
    va
    @2
    cI
    cvv
    @10
    @11
    tdeglem1
    #
    @1
    cn0
    @2
    frn
    3syl
    syl5ss
    adantr
    #
    cn0
    @7
    ssun1
    syl6ss
    @15
    @5
    cfn
    wcel
    #
    @14
    @5
    cxr
    wss
    #
    @6
    @5
    wcel
    #
    @0
    @22
    @14
    @0
    @2
    wfun
    #
    @4
    cfn
    wcel
    @22
    @0
    @17
    @18
    @25
    @19
    @20
    @1
    cn0
    @2
    ffun
    3syl
    @0
    cF
    @3
    @0
    cB
    cP
    cR
    cF
    cI
    cvv
    @3
    mdegcl.p
    mdegcl.b
    @9
    @0
    id
    @0
    @17
    cR
    cvv
    wcel
    cF
    cB
    cP
    cmpl
    cI
    cR
    reldmmpl
    mdegcl.p
    mdegcl.b
    elbasov
    simprd
    mplelsfi
    fsuppimpd
    @2
    @4
    imafi
    syl2anc
    adantr
    @0
    @14
    simpr
    @15
    @5
    cn0
    cxr
    @21
    cn0
    cr
    cxr
    nn0ssre
    ressxr
    sstri
    syl6ss
    cxr
    clt
    wor
    @22
    @14
    @23
    w3a
    @24
    xrltso
    cxr
    @5
    clt
    fisupcl
    mpan
    syl3anc
    sseldd
    @13
    @0
    @12
    cmnf
    @8
    xrsup0
    @7
    @8
    cmnf
    @7
    cn0
    ssun2
    cmnf
    cmnf
    cxr
    mnfxr
    elexi
    snid
    sselii
    eqeltri
    a1i
    pm2.61ne
    eqeltrd
end
