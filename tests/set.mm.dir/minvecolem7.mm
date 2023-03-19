include "cv.mm"
include "co.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wreu.mm"
include "minvecolem5.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "cc0.mm"
include "caddc.mm"
include "c4.mm"
include "cmul.mm"
include "ccphlo.mm"
include "ad2antrr.mm"
include "css.mm"
include "ccbn.mm"
include "cin.mm"
include "cr.mm"
include "0re.mm"
include "a1i.mm"
include "0le0.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprl.mm"
include "simprr.mm"
include "minvecolem2.mm"
include "ex.mm"
include "wb.mm"
include "minvecolem6.mm"
include "adantrr.mm"
include "adantrl.mm"
include "anbi12d.mm"
include "4cn.mm"
include "mul01i.mm"
include "breq2i.mm"
include "cme.mm"
include "cnv.mm"
include "phnv.mm"
include "syl.mm"
include "adantr.mm"
include "imsmet.mm"
include "wss.mm"
include "inss1.mm"
include "sseldi.mm"
include "eqid.mm"
include "sspba.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "metcl.mm"
include "syl3anc.mm"
include "sqge0d.mm"
include "biantrud.mm"
include "resqcld.mm"
include "letri3.mm"
include "sylancl.mm"
include "cc.mm"
include "recnd.mm"
include "sqeq0.mm"
include "meteq0.mm"
include "bitrd.mm"
include "3bitr2d.mm"
include "syl5bb.mm"
include "3imtr3d.mm"
include "ralrimivva.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "ralbidv.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem minvecolem7
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
  assert |- ( ph -> E! x e. Y A. y e. Y ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) )

  proof
    wph
    cA
    vx
    cv
    #
    cM
    co
    #
    cN
    cfv
    #
    cA
    vy
    cv
    cM
    co
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
    vx
    cY
    wrex
    @5
    cA
    vw
    cv
    #
    cM
    co
    #
    cN
    cfv
    #
    @3
    cle
    wbr
    #
    vy
    cY
    wral
    #
    wa
    #
    @0
    @6
    wceq
    #
    wi
    #
    vw
    cY
    wral
    vx
    cY
    wral
    @5
    vx
    cY
    wreu
    wph
    vx
    vy
    cA
    cD
    cR
    cS
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
    minveco.s
    minvecolem5
    wph
    @13
    vx
    vw
    cY
    cY
    wph
    @0
    cY
    wcel
    #
    @6
    cY
    wcel
    #
    wa
    #
    wa
    #
    cA
    @0
    cD
    co
    c2
    cexp
    co
    cS
    c2
    cexp
    co
    cc0
    caddc
    co
    #
    cle
    wbr
    #
    cA
    @6
    cD
    co
    c2
    cexp
    co
    @18
    cle
    wbr
    #
    wa
    #
    @0
    @6
    cD
    co
    #
    c2
    cexp
    co
    #
    c4
    cc0
    cmul
    co
    #
    cle
    wbr
    #
    @11
    @12
    @17
    @21
    @25
    @17
    @21
    wa
    #
    vy
    cA
    cc0
    cD
    cR
    cS
    cU
    cJ
    @0
    @6
    cM
    cN
    cW
    cX
    cY
    minveco.x
    minveco.m
    minveco.n
    minveco.y
    wph
    cU
    ccphlo
    wcel
    #
    @16
    @21
    minveco.u
    ad2antrr
    wph
    cW
    cU
    css
    cfv
    #
    ccbn
    cin
    #
    wcel
    @16
    @21
    minveco.w
    ad2antrr
    wph
    cA
    cX
    wcel
    @16
    @21
    minveco.a
    ad2antrr
    minveco.d
    minveco.j
    minveco.r
    minveco.s
    cc0
    cr
    wcel
    #
    @26
    0re
    a1i
    cc0
    cc0
    cle
    wbr
    @26
    0le0
    a1i
    wph
    @14
    @15
    @21
    simplrl
    wph
    @14
    @15
    @21
    simplrr
    @17
    @19
    @20
    simprl
    @17
    @19
    @20
    simprr
    minvecolem2
    ex
    @17
    @19
    @5
    @20
    @10
    wph
    @14
    @19
    @5
    wb
    @15
    wph
    vx
    vy
    cA
    cD
    cR
    cS
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
    minveco.s
    minvecolem6
    adantrr
    wph
    @15
    @20
    @10
    wb
    @14
    wph
    vw
    vy
    cA
    cD
    cR
    cS
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
    minveco.s
    minvecolem6
    adantrl
    anbi12d
    @25
    @23
    cc0
    cle
    wbr
    #
    @17
    @12
    @24
    cc0
    @23
    cle
    c4
    4cn
    mul01i
    breq2i
    @17
    @31
    @31
    cc0
    @23
    cle
    wbr
    #
    wa
    #
    @23
    cc0
    wceq
    #
    @12
    @17
    @32
    @31
    @17
    @22
    @17
    cD
    cX
    cme
    cfv
    wcel
    #
    @0
    cX
    wcel
    #
    @6
    cX
    wcel
    #
    @22
    cr
    wcel
    @17
    cU
    cnv
    wcel
    #
    @35
    wph
    @38
    @16
    wph
    @27
    @38
    minveco.u
    cU
    phnv
    syl
    #
    adantr
    cD
    cU
    cX
    minveco.x
    minveco.d
    imsmet
    syl
    #
    @17
    cY
    cX
    @0
    wph
    cY
    cX
    wss
    #
    @16
    wph
    @38
    cW
    @28
    wcel
    @41
    @39
    wph
    @29
    @28
    cW
    @28
    ccbn
    inss1
    minveco.w
    sseldi
    cU
    @28
    cW
    cX
    cY
    minveco.x
    minveco.y
    @28
    eqid
    sspba
    syl2anc
    adantr
    #
    wph
    @14
    @15
    simprl
    sseldd
    #
    @17
    cY
    cX
    @6
    @42
    wph
    @14
    @15
    simprr
    sseldd
    #
    @0
    @6
    cD
    cX
    metcl
    syl3anc
    #
    sqge0d
    biantrud
    @17
    @23
    cr
    wcel
    @30
    @34
    @33
    wb
    @17
    @22
    @45
    resqcld
    0re
    @23
    cc0
    letri3
    sylancl
    @17
    @34
    @22
    cc0
    wceq
    #
    @12
    @17
    @22
    cc
    wcel
    @34
    @46
    wb
    @17
    @22
    @45
    recnd
    @22
    sqeq0
    syl
    @17
    @35
    @36
    @37
    @46
    @12
    wb
    @40
    @43
    @44
    @0
    @6
    cD
    cX
    meteq0
    syl3anc
    bitrd
    3bitr2d
    syl5bb
    3imtr3d
    ralrimivva
    @5
    @10
    vx
    vw
    cY
    @12
    @4
    @9
    vy
    cY
    @12
    @2
    @8
    @3
    cle
    @12
    @1
    @7
    cN
    @0
    @6
    cA
    cM
    oveq2
    fveq2d
    breq1d
    ralbidv
    reu4
    sylanbrc
end
