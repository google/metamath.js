include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cc0.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "co.mm"
include "cfv.mm"
include "cmpt.mm"
include "crn.mm"
include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "cnv.mm"
include "ccphlo.mm"
include "phnv.mm"
include "syl.mm"
include "adantr.mm"
include "css.mm"
include "ccbn.mm"
include "cin.mm"
include "elin.mm"
include "sylib.mm"
include "simpld.mm"
include "eqid.mm"
include "sspba.mm"
include "syl2anc.mm"
include "sselda.mm"
include "nvmcl.mm"
include "syl3anc.mm"
include "nvcl.mm"
include "fmptd.mm"
include "frn.mm"
include "syl5eqss.mm"
include "cdm.mm"
include "cn0v.mm"
include "simprd.mm"
include "bnnv.mm"
include "nvzcl.mm"
include "3syl.mm"
include "fvex.mm"
include "dmmpti.mm"
include "syl6eleqr.mm"
include "ne0i.mm"
include "wceq.mm"
include "dm0rn0.mm"
include "eqeq1i.mm"
include "bitr4i.mm"
include "necon3bii.mm"
include "nvge0.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "wb.mm"
include "rgenw.mm"
include "breq2.mm"
include "ralrnmpt.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "raleqi.mm"
include "3jca.mm"

theorem minvecolem1
  let wph: wff ph
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cD: class D
  let cR: class R
  let cU: class U
  let cJ: class J
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vn: setvar n
  let vx: setvar x
  let cF: class F
  let vk: setvar k
  let cK: class K
  let cL: class L
  let vf: setvar f
  let cS: class S
  let cT: class T
  assume minveco.x: |- X = ( BaseSet ` U )
  assume minveco.m: |- M = ( -v ` U )
  assume minveco.n: |- N = ( normCV ` U )
  assume minveco.y: |- Y = ( BaseSet ` W )
  assume minveco.u: |- ( ph -> U e. CPreHilOLD )
  assume minveco.w: |- ( ph -> W e. ( ( SubSp ` U ) i^i CBan ) )
  assume minveco.a: |- ( ph -> A e. X )
  assume minveco.d: |- D = ( IndMet ` U )
  assume minveco.j: |- J = ( MetOpen ` D )
  assume minveco.r: |- R = ran ( y e. Y |-> ( N ` ( A M y ) ) )

  disjoint w y
  disjoint J w
  disjoint J y
  disjoint M w
  disjoint M y
  disjoint N w
  disjoint N y
  disjoint ph w
  disjoint ph y
  disjoint R w
  disjoint A w
  disjoint A y
  disjoint D w
  disjoint D y
  disjoint U w
  disjoint U y
  disjoint W w
  disjoint W y
  disjoint X w
  disjoint Y w
  disjoint Y y
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint J k
  disjoint n w
  disjoint J n
  disjoint w x
  disjoint J x
  disjoint K y
  disjoint L y
  disjoint f j
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint M f
  disjoint j w
  disjoint M j
  disjoint M x
  disjoint N f
  disjoint N j
  disjoint N x
  disjoint f k
  disjoint f n
  disjoint f ph
  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph x
  disjoint R x
  disjoint S f
  disjoint S k
  disjoint S n
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint A f
  disjoint A j
  disjoint A k
  disjoint A n
  disjoint A x
  disjoint D f
  disjoint D j
  disjoint D k
  disjoint D n
  disjoint D x
  disjoint U x
  disjoint W x
  disjoint T n
  disjoint X j
  disjoint X k
  disjoint X n
  disjoint X x
  disjoint Y f
  disjoint Y j
  disjoint Y k
  disjoint Y n
  disjoint Y x
  assert |- ( ph -> ( R C_ RR /\ R =/= (/) /\ A. w e. R 0 <_ w ) )

  proof
    wph
    cR
    cr
    wss
    cR
    c0
    wne
    #
    cc0
    vw
    cv
    #
    cle
    wbr
    #
    vw
    cR
    wral
    #
    wph
    cR
    vy
    cY
    cA
    vy
    cv
    #
    cM
    co
    #
    cN
    cfv
    #
    cmpt
    #
    crn
    #
    cr
    minveco.r
    wph
    cY
    cr
    @7
    wf
    @8
    cr
    wss
    wph
    vy
    cY
    @6
    cr
    @7
    wph
    @4
    cY
    wcel
    #
    wa
    #
    cU
    cnv
    wcel
    #
    @5
    cX
    wcel
    #
    @6
    cr
    wcel
    wph
    @11
    @9
    wph
    cU
    ccphlo
    wcel
    @11
    minveco.u
    cU
    phnv
    syl
    #
    adantr
    #
    @10
    @11
    cA
    cX
    wcel
    #
    @4
    cX
    wcel
    @12
    @14
    wph
    @15
    @9
    minveco.a
    adantr
    wph
    cY
    cX
    @4
    wph
    @11
    cW
    cU
    css
    cfv
    #
    wcel
    #
    cY
    cX
    wss
    @13
    wph
    @17
    cW
    ccbn
    wcel
    #
    wph
    cW
    @16
    ccbn
    cin
    wcel
    @17
    @18
    wa
    minveco.w
    cW
    @16
    ccbn
    elin
    sylib
    #
    simpld
    cU
    @16
    cW
    cX
    cY
    minveco.x
    minveco.y
    @16
    eqid
    sspba
    syl2anc
    sselda
    cA
    @4
    cU
    cM
    cX
    minveco.x
    minveco.m
    nvmcl
    syl3anc
    #
    @5
    cU
    cN
    cX
    minveco.x
    minveco.n
    nvcl
    syl2anc
    @7
    eqid
    #
    fmptd
    cY
    cr
    @7
    frn
    syl
    syl5eqss
    wph
    @7
    cdm
    #
    c0
    wne
    #
    @0
    wph
    cW
    cn0v
    cfv
    #
    @22
    wcel
    @23
    wph
    @24
    cY
    @22
    wph
    @18
    cW
    cnv
    wcel
    @24
    cY
    wcel
    wph
    @17
    @18
    @19
    simprd
    cW
    bnnv
    cW
    cY
    @24
    minveco.y
    @24
    eqid
    nvzcl
    3syl
    vy
    cY
    @6
    @7
    @5
    cN
    fvex
    #
    @21
    dmmpti
    syl6eleqr
    @22
    @24
    ne0i
    syl
    @22
    c0
    cR
    c0
    @22
    c0
    wceq
    @8
    c0
    wceq
    cR
    c0
    wceq
    @7
    dm0rn0
    cR
    @8
    c0
    minveco.r
    eqeq1i
    bitr4i
    necon3bii
    sylib
    wph
    @2
    vw
    @8
    wral
    #
    @3
    wph
    cc0
    @6
    cle
    wbr
    #
    vy
    cY
    wral
    #
    @26
    wph
    @27
    vy
    cY
    @10
    @11
    @12
    @27
    @14
    @20
    @5
    cU
    cN
    cX
    minveco.x
    minveco.n
    nvge0
    syl2anc
    ralrimiva
    @6
    cvv
    wcel
    #
    vy
    cY
    wral
    @26
    @28
    wb
    @29
    vy
    cY
    @25
    rgenw
    @2
    @27
    vy
    vw
    cY
    @6
    @7
    cvv
    @21
    @1
    @6
    cc0
    cle
    breq2
    ralrnmpt
    ax-mp
    sylibr
    @2
    vw
    cR
    @8
    minveco.r
    raleqi
    sylibr
    3jca
end
