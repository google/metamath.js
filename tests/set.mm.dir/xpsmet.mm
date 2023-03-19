include "cxp.mm"
include "csca.mm"
include "cfv.mm"
include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cprds.mm"
include "cds.mm"
include "cv.mm"
include "cmpt2.mm"
include "crn.mm"
include "cres.mm"
include "cvv.mm"
include "eqid.mm"
include "xpsval.mm"
include "xpslem.mm"
include "wf1o.mm"
include "xpsff1o2.mm"
include "f1ocnv.mm"
include "mp1i.mm"
include "ovexd.mm"
include "cme.mm"
include "wcel.mm"
include "wss.mm"
include "c2o.mm"
include "cmpt.mm"
include "cbs.mm"
include "fvexd.mm"
include "com.mm"
include "cfn.mm"
include "2onn.mm"
include "nnfi.mm"
include "wa.mm"
include "c0.mm"
include "wceq.mm"
include "c1o.mm"
include "wo.mm"
include "cpr.mm"
include "elpri.mm"
include "df2o3.mm"
include "eleq2s.mm"
include "adantr.mm"
include "fveq2.mm"
include "xpsc0.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "sqxpeqd.mm"
include "reseq12d.mm"
include "3eltr4d.mm"
include "xpsc1.mm"
include "jaodan.mm"
include "sylan2.mm"
include "prdsmet.mm"
include "wfn.mm"
include "xpscfn.mm"
include "syl2anc.mm"
include "dffn5.mm"
include "sylib.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "ssid.mm"
include "metres2.mm"
include "sylancl.mm"
include "imasf1omet.mm"

theorem xpsmet
  let wph: wff ph
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume xpsds.t: |- T = ( R Xs. S )
  assume xpsds.x: |- X = ( Base ` R )
  assume xpsds.y: |- Y = ( Base ` S )
  assume xpsds.1: |- ( ph -> R e. V )
  assume xpsds.2: |- ( ph -> S e. W )
  assume xpsds.p: |- P = ( dist ` T )
  assume xpsds.m: |- M = ( ( dist ` R ) |` ( X X. X ) )
  assume xpsds.n: |- N = ( ( dist ` S ) |` ( Y X. Y ) )
  assume xpsmet.3: |- ( ph -> M e. ( Met ` X ) )
  assume xpsmet.4: |- ( ph -> N e. ( Met ` Y ) )


  assert |- ( ph -> P e. ( Met ` ( X X. Y ) ) )

  proof
    wph
    cX
    cY
    cxp
    #
    cP
    cR
    csca
    cfv
    #
    cR
    csn
    cS
    csn
    ccda
    co
    ccnv
    #
    cprds
    co
    #
    cT
    @3
    cds
    cfv
    #
    vx
    vy
    cX
    cY
    vx
    cv
    csn
    vy
    cv
    csn
    ccda
    co
    ccnv
    cmpt2
    #
    crn
    #
    @6
    cxp
    cres
    #
    @5
    ccnv
    #
    @6
    cvv
    wph
    vx
    vy
    cR
    cS
    cT
    @3
    @5
    @1
    cV
    cW
    cX
    cY
    xpsds.t
    xpsds.x
    xpsds.y
    xpsds.1
    xpsds.2
    @5
    eqid
    #
    @1
    eqid
    #
    @3
    eqid
    #
    xpsval
    wph
    vx
    vy
    cR
    cS
    cT
    @3
    @5
    @1
    cV
    cW
    cX
    cY
    xpsds.t
    xpsds.x
    xpsds.y
    xpsds.1
    xpsds.2
    @9
    @10
    @11
    xpslem
    #
    @0
    @6
    @5
    wf1o
    @6
    @0
    @8
    wf1o
    wph
    vx
    vy
    cX
    cY
    @5
    @9
    xpsff1o2
    @0
    @6
    @5
    f1ocnv
    mp1i
    wph
    @1
    @2
    cprds
    ovexd
    @7
    eqid
    xpsds.p
    wph
    @4
    @6
    cme
    cfv
    #
    wcel
    @6
    @6
    wss
    @7
    @13
    wcel
    wph
    @1
    vk
    c2o
    vk
    cv
    #
    @2
    cfv
    #
    cmpt
    #
    cprds
    co
    #
    cds
    cfv
    #
    @17
    cbs
    cfv
    #
    cme
    cfv
    @4
    @13
    wph
    vk
    @19
    @18
    @15
    @1
    @15
    cds
    cfv
    #
    @15
    cbs
    cfv
    #
    @21
    cxp
    #
    cres
    #
    c2o
    @21
    cvv
    @17
    cvv
    @17
    eqid
    @19
    eqid
    @21
    eqid
    @23
    eqid
    @18
    eqid
    wph
    cR
    csca
    fvexd
    c2o
    com
    wcel
    c2o
    cfn
    wcel
    wph
    2onn
    c2o
    nnfi
    mp1i
    wph
    @14
    c2o
    wcel
    #
    wa
    @14
    @2
    fvexd
    @24
    wph
    @14
    c0
    wceq
    #
    @14
    c1o
    wceq
    #
    wo
    #
    @23
    @21
    cme
    cfv
    #
    wcel
    #
    @27
    @14
    c0
    c1o
    cpr
    c2o
    @14
    c0
    c1o
    elpri
    df2o3
    eleq2s
    wph
    @25
    @29
    @26
    wph
    @25
    wa
    #
    cM
    cX
    cme
    cfv
    #
    @23
    @28
    wph
    cM
    @31
    wcel
    @25
    xpsmet.3
    adantr
    @30
    @23
    cR
    cds
    cfv
    #
    cX
    cX
    cxp
    #
    cres
    cM
    @30
    @20
    @32
    @22
    @33
    @30
    @15
    cR
    cds
    @25
    wph
    @15
    c0
    @2
    cfv
    #
    cR
    @14
    c0
    @2
    fveq2
    wph
    cR
    cV
    wcel
    #
    @34
    cR
    wceq
    xpsds.1
    cR
    cS
    cV
    xpsc0
    syl
    sylan9eqr
    #
    fveq2d
    @30
    @21
    cX
    @30
    @21
    cR
    cbs
    cfv
    cX
    @30
    @15
    cR
    cbs
    @36
    fveq2d
    xpsds.x
    syl6eqr
    #
    sqxpeqd
    reseq12d
    xpsds.m
    syl6eqr
    @30
    @21
    cX
    cme
    @37
    fveq2d
    3eltr4d
    wph
    @26
    wa
    #
    cN
    cY
    cme
    cfv
    #
    @23
    @28
    wph
    cN
    @39
    wcel
    @26
    xpsmet.4
    adantr
    @38
    @23
    cS
    cds
    cfv
    #
    cY
    cY
    cxp
    #
    cres
    cN
    @38
    @20
    @40
    @22
    @41
    @38
    @15
    cS
    cds
    @26
    wph
    @15
    c1o
    @2
    cfv
    #
    cS
    @14
    c1o
    @2
    fveq2
    wph
    cS
    cW
    wcel
    #
    @42
    cS
    wceq
    xpsds.2
    cR
    cS
    cW
    xpsc1
    syl
    sylan9eqr
    #
    fveq2d
    @38
    @21
    cY
    @38
    @21
    cS
    cbs
    cfv
    cY
    @38
    @15
    cS
    cbs
    @44
    fveq2d
    xpsds.y
    syl6eqr
    #
    sqxpeqd
    reseq12d
    xpsds.n
    syl6eqr
    @38
    @21
    cY
    cme
    @45
    fveq2d
    3eltr4d
    jaodan
    sylan2
    prdsmet
    wph
    @3
    @17
    cds
    wph
    @2
    @16
    @1
    cprds
    wph
    @2
    c2o
    wfn
    #
    @2
    @16
    wceq
    wph
    @35
    @43
    @46
    xpsds.1
    xpsds.2
    cR
    cS
    cV
    cW
    xpscfn
    syl2anc
    vk
    c2o
    @2
    dffn5
    sylib
    oveq2d
    #
    fveq2d
    wph
    @6
    @19
    cme
    wph
    @6
    @3
    cbs
    cfv
    @19
    @12
    wph
    @3
    @17
    cbs
    @47
    fveq2d
    eqtrd
    fveq2d
    3eltr4d
    @6
    ssid
    @4
    @6
    @6
    metres2
    sylancl
    imasf1omet
end
