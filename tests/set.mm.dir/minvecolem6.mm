include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cc0.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "wral.mm"
include "cnv.mm"
include "wceq.mm"
include "ccphlo.mm"
include "phnv.mm"
include "syl.mm"
include "adantr.mm"
include "css.mm"
include "wss.mm"
include "ccbn.mm"
include "cin.mm"
include "inss1.mm"
include "sseldi.mm"
include "eqid.mm"
include "sspba.mm"
include "syl2anc.mm"
include "sselda.mm"
include "imsdval.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "w3a.mm"
include "minvecolem1.mm"
include "simp1d.mm"
include "simp2d.mm"
include "0red.mm"
include "simp3d.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "infrecl.mm"
include "syl5eqel.mm"
include "resqcld.mm"
include "recnd.mm"
include "addid1d.mm"
include "breq12d.mm"
include "nvmcl.mm"
include "nvcl.mm"
include "nvge0.mm"
include "wb.mm"
include "infregelb.mm"
include "syl31anc.mm"
include "mpbird.mm"
include "syl6breqr.mm"
include "le2sqd.mm"
include "breq2i.mm"
include "syl5bb.mm"
include "3bitr2d.mm"
include "cmpt.mm"
include "crn.mm"
include "raleqi.mm"
include "cvv.mm"
include "fvex.mm"
include "rgenw.mm"
include "breq2.mm"
include "ralrnmpt.mm"
include "ax-mp.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem minvecolem6
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let cS: class S
  let cU: class U
  let cJ: class J
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  let vw: setvar w
  let cK: class K
  let cL: class L
  let vf: setvar f
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
  assume minveco.s: |- S = inf ( R , RR , < )

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint S x
  disjoint S y
  disjoint A x
  disjoint A y
  disjoint D x
  disjoint D y
  disjoint U x
  disjoint U y
  disjoint W x
  disjoint W y
  disjoint X x
  disjoint Y x
  disjoint Y y
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint n x
  disjoint n y
  disjoint F n
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
  disjoint w y
  disjoint J w
  disjoint K y
  disjoint L y
  disjoint f j
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint M f
  disjoint j w
  disjoint M j
  disjoint M w
  disjoint N f
  disjoint N j
  disjoint N w
  disjoint f k
  disjoint f n
  disjoint f ph
  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph w
  disjoint R w
  disjoint S f
  disjoint S k
  disjoint S n
  disjoint S w
  disjoint A f
  disjoint A j
  disjoint A k
  disjoint A n
  disjoint A w
  disjoint D f
  disjoint D j
  disjoint D k
  disjoint D n
  disjoint D w
  disjoint U w
  disjoint W w
  disjoint T n
  disjoint X j
  disjoint X k
  disjoint X n
  disjoint X w
  disjoint Y f
  disjoint Y j
  disjoint Y k
  disjoint Y n
  disjoint Y w
  assert |- ( ( ph /\ x e. Y ) -> ( ( ( A D x ) ^ 2 ) <_ ( ( S ^ 2 ) + 0 ) <-> A. y e. Y ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) ) )

  proof
    wph
    vx
    cv
    #
    cY
    wcel
    #
    wa
    #
    cA
    @0
    cD
    co
    #
    c2
    cexp
    co
    #
    cS
    c2
    cexp
    co
    #
    cc0
    caddc
    co
    #
    cle
    wbr
    #
    cA
    @0
    cM
    co
    #
    cN
    cfv
    #
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
    @9
    cA
    vy
    cv
    cM
    co
    #
    cN
    cfv
    #
    cle
    wbr
    #
    vy
    cY
    wral
    #
    @2
    @7
    @9
    c2
    cexp
    co
    #
    @5
    cle
    wbr
    @9
    cS
    cle
    wbr
    #
    @12
    @2
    @4
    @17
    @6
    @5
    cle
    @2
    @3
    @9
    c2
    cexp
    @2
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    @0
    cX
    wcel
    #
    @3
    @9
    wceq
    wph
    @19
    @1
    wph
    cU
    ccphlo
    wcel
    @19
    minveco.u
    cU
    phnv
    syl
    #
    adantr
    #
    wph
    @20
    @1
    minveco.a
    adantr
    #
    wph
    cY
    cX
    @0
    wph
    @19
    cW
    cU
    css
    cfv
    #
    wcel
    cY
    cX
    wss
    @22
    wph
    @25
    ccbn
    cin
    @25
    cW
    @25
    ccbn
    inss1
    minveco.w
    sseldi
    cU
    @25
    cW
    cX
    cY
    minveco.x
    minveco.y
    @25
    eqid
    sspba
    syl2anc
    sselda
    #
    cA
    @0
    cD
    cU
    cM
    cN
    cX
    minveco.x
    minveco.m
    minveco.n
    minveco.d
    imsdval
    syl3anc
    oveq1d
    @2
    @5
    @2
    @5
    @2
    cS
    @2
    cS
    cR
    cr
    clt
    cinf
    #
    cr
    minveco.s
    @2
    cR
    cr
    wss
    #
    cR
    c0
    wne
    #
    @0
    @10
    cle
    wbr
    #
    vw
    cR
    wral
    #
    vx
    cr
    wrex
    #
    @27
    cr
    wcel
    @2
    @28
    @29
    cc0
    @10
    cle
    wbr
    #
    vw
    cR
    wral
    #
    wph
    @28
    @29
    @34
    w3a
    @1
    wph
    vy
    vw
    cA
    cD
    cR
    cU
    cJ
    cM
    cN
    cW
    cX
    cY
    minveco.x
    minveco.m
    minveco.n
    minveco.y
    minveco.u
    minveco.w
    minveco.a
    minveco.d
    minveco.j
    minveco.r
    minvecolem1
    adantr
    #
    simp1d
    #
    @2
    @28
    @29
    @34
    @35
    simp2d
    #
    @2
    cc0
    cr
    wcel
    #
    @34
    @32
    @2
    0red
    #
    @2
    @28
    @29
    @34
    @35
    simp3d
    #
    @31
    @34
    vx
    cc0
    cr
    @0
    cc0
    wceq
    @30
    @33
    vw
    cR
    @0
    cc0
    @10
    cle
    breq1
    ralbidv
    rspcev
    syl2anc
    #
    vx
    vw
    cR
    infrecl
    syl3anc
    syl5eqel
    #
    resqcld
    recnd
    addid1d
    breq12d
    @2
    @9
    cS
    @2
    @19
    @8
    cX
    wcel
    #
    @9
    cr
    wcel
    #
    @23
    @2
    @19
    @20
    @21
    @43
    @23
    @24
    @26
    cA
    @0
    cU
    cM
    cX
    minveco.x
    minveco.m
    nvmcl
    syl3anc
    #
    @8
    cU
    cN
    cX
    minveco.x
    minveco.n
    nvcl
    syl2anc
    #
    @42
    @2
    @19
    @43
    cc0
    @9
    cle
    wbr
    @23
    @45
    @8
    cU
    cN
    cX
    minveco.x
    minveco.n
    nvge0
    syl2anc
    @2
    cc0
    @27
    cS
    cle
    @2
    cc0
    @27
    cle
    wbr
    #
    @34
    @40
    @2
    @28
    @29
    @32
    @38
    @47
    @34
    wb
    @36
    @37
    @41
    @39
    vx
    vw
    vw
    cR
    cc0
    infregelb
    syl31anc
    mpbird
    minveco.s
    syl6breqr
    le2sqd
    @18
    @9
    @27
    cle
    wbr
    #
    @2
    @12
    cS
    @27
    @9
    cle
    minveco.s
    breq2i
    @2
    @28
    @29
    @32
    @44
    @48
    @12
    wb
    @36
    @37
    @41
    @46
    vx
    vw
    vw
    cR
    @9
    infregelb
    syl31anc
    syl5bb
    3bitr2d
    @12
    @11
    vw
    vy
    cY
    @14
    cmpt
    #
    crn
    #
    wral
    #
    @16
    @11
    vw
    cR
    @50
    minveco.r
    raleqi
    @14
    cvv
    wcel
    #
    vy
    cY
    wral
    @51
    @16
    wb
    @52
    vy
    cY
    @13
    cN
    fvex
    rgenw
    @11
    @15
    vy
    vw
    cY
    @14
    @49
    cvv
    @49
    eqid
    @10
    @14
    @9
    cle
    breq2
    ralrnmpt
    ax-mp
    bitri
    syl6bb
end
