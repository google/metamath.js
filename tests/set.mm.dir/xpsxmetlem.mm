include "csca.mm"
include "cfv.mm"
include "c2o.mm"
include "cv.mm"
include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cmpt.mm"
include "cprds.mm"
include "cds.mm"
include "cbs.mm"
include "cxmt.mm"
include "cmpt2.mm"
include "crn.mm"
include "cxp.mm"
include "cres.mm"
include "cvv.mm"
include "con0.mm"
include "eqid.mm"
include "fvexd.mm"
include "wcel.mm"
include "2on.mm"
include "a1i.mm"
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
include "prdsxmet.mm"
include "wfn.mm"
include "xpscfn.mm"
include "syl2anc.mm"
include "dffn5.mm"
include "sylib.mm"
include "oveq2d.mm"
include "xpslem.mm"
include "eqtrd.mm"

theorem xpsxmetlem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
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
  assume xpsds.3: |- ( ph -> M e. ( *Met ` X ) )
  assume xpsds.4: |- ( ph -> N e. ( *Met ` Y ) )

  disjoint x y
  disjoint M x
  disjoint N x
  disjoint ph x
  disjoint R x
  disjoint S x
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint W x
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint A x
  disjoint A y
  disjoint k ph
  disjoint R k
  disjoint S k
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint C k
  disjoint C x
  disjoint C y
  disjoint D k
  disjoint D x
  disjoint D y
  assert |- ( ph -> ( dist ` ( ( Scalar ` R ) Xs_ `' ( { R } +c { S } ) ) ) e. ( *Met ` ran ( x e. X , y e. Y |-> `' ( { x } +c { y } ) ) ) )

  proof
    wph
    cR
    csca
    cfv
    #
    vk
    c2o
    vk
    cv
    #
    cR
    csn
    cS
    csn
    ccda
    co
    ccnv
    #
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
    @5
    cbs
    cfv
    #
    cxmt
    cfv
    @0
    @2
    cprds
    co
    #
    cds
    cfv
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
    cxmt
    cfv
    wph
    vk
    @7
    @6
    @3
    @0
    @3
    cds
    cfv
    #
    @3
    cbs
    cfv
    #
    @12
    cxp
    #
    cres
    #
    c2o
    @12
    cvv
    con0
    @5
    cvv
    @5
    eqid
    @7
    eqid
    @12
    eqid
    @14
    eqid
    @6
    eqid
    wph
    cR
    csca
    fvexd
    c2o
    con0
    wcel
    wph
    2on
    a1i
    wph
    @1
    c2o
    wcel
    #
    wa
    @1
    @2
    fvexd
    @15
    wph
    @1
    c0
    wceq
    #
    @1
    c1o
    wceq
    #
    wo
    #
    @14
    @12
    cxmt
    cfv
    #
    wcel
    #
    @18
    @1
    c0
    c1o
    cpr
    c2o
    @1
    c0
    c1o
    elpri
    df2o3
    eleq2s
    wph
    @16
    @20
    @17
    wph
    @16
    wa
    #
    cM
    cX
    cxmt
    cfv
    #
    @14
    @19
    wph
    cM
    @22
    wcel
    @16
    xpsds.3
    adantr
    @21
    @14
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
    @21
    @11
    @23
    @13
    @24
    @21
    @3
    cR
    cds
    @16
    wph
    @3
    c0
    @2
    cfv
    #
    cR
    @1
    c0
    @2
    fveq2
    wph
    cR
    cV
    wcel
    #
    @25
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
    @21
    @12
    cX
    @21
    @12
    cR
    cbs
    cfv
    cX
    @21
    @3
    cR
    cbs
    @27
    fveq2d
    xpsds.x
    syl6eqr
    #
    sqxpeqd
    reseq12d
    xpsds.m
    syl6eqr
    @21
    @12
    cX
    cxmt
    @28
    fveq2d
    3eltr4d
    wph
    @17
    wa
    #
    cN
    cY
    cxmt
    cfv
    #
    @14
    @19
    wph
    cN
    @30
    wcel
    @17
    xpsds.4
    adantr
    @29
    @14
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
    @29
    @11
    @31
    @13
    @32
    @29
    @3
    cS
    cds
    @17
    wph
    @3
    c1o
    @2
    cfv
    #
    cS
    @1
    c1o
    @2
    fveq2
    wph
    cS
    cW
    wcel
    #
    @33
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
    @29
    @12
    cY
    @29
    @12
    cS
    cbs
    cfv
    cY
    @29
    @3
    cS
    cbs
    @35
    fveq2d
    xpsds.y
    syl6eqr
    #
    sqxpeqd
    reseq12d
    xpsds.n
    syl6eqr
    @29
    @12
    cY
    cxmt
    @36
    fveq2d
    3eltr4d
    jaodan
    sylan2
    prdsxmet
    wph
    @8
    @5
    cds
    wph
    @2
    @4
    @0
    cprds
    wph
    @2
    c2o
    wfn
    #
    @2
    @4
    wceq
    wph
    @26
    @34
    @37
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
    @10
    @7
    cxmt
    wph
    @10
    @8
    cbs
    cfv
    @7
    wph
    vx
    vy
    cR
    cS
    cT
    @8
    @9
    @0
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
    eqid
    @0
    eqid
    @8
    eqid
    xpslem
    wph
    @8
    @5
    cbs
    @38
    fveq2d
    eqtrd
    fveq2d
    3eltr4d
end
