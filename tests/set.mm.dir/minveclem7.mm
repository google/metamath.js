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
include "minveclem5.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "cc0.mm"
include "caddc.mm"
include "c4.mm"
include "cmul.mm"
include "ccph.mm"
include "ad2antrr.mm"
include "clss.mm"
include "cress.mm"
include "ccms.mm"
include "cr.mm"
include "0re.mm"
include "a1i.mm"
include "0le0.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprl.mm"
include "simprr.mm"
include "minveclem2.mm"
include "ex.mm"
include "wb.mm"
include "minveclem6.mm"
include "adantrr.mm"
include "adantrl.mm"
include "anbi12d.mm"
include "4cn.mm"
include "mul01i.mm"
include "breq2i.mm"
include "cme.mm"
include "cmt.mm"
include "cngp.mm"
include "cphngp.mm"
include "ngpms.mm"
include "3syl.mm"
include "adantr.mm"
include "msmet.mm"
include "syl.mm"
include "wss.mm"
include "eqid.mm"
include "lssss.mm"
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

theorem minveclem7
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let cS: class S
  let cU: class U
  let cJ: class J
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vw: setvar w
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let cP: class P
  let cF: class F
  let cK: class K
  let cT: class T
  let cL: class L
  assume minvec.x: |- X = ( Base ` U )
  assume minvec.m: |- .- = ( -g ` U )
  assume minvec.n: |- N = ( norm ` U )
  assume minvec.u: |- ( ph -> U e. CPreHil )
  assume minvec.y: |- ( ph -> Y e. ( LSubSp ` U ) )
  assume minvec.w: |- ( ph -> ( U |`s Y ) e. CMetSp )
  assume minvec.a: |- ( ph -> A e. X )
  assume minvec.j: |- J = ( TopOpen ` U )
  assume minvec.r: |- R = ran ( y e. Y |-> ( N ` ( A .- y ) ) )
  assume minvec.s: |- S = inf ( R , RR , < )
  assume minvec.d: |- D = ( ( dist ` U ) |` ( X X. X ) )

  disjoint x y
  disjoint .- x
  disjoint .- y
  disjoint A x
  disjoint A y
  disjoint J x
  disjoint J y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint U x
  disjoint U y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint D x
  disjoint D y
  disjoint S x
  disjoint S y
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint .- j
  disjoint w x
  disjoint w y
  disjoint .- w
  disjoint j r
  disjoint j s
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j z
  disjoint A j
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint J r
  disjoint J w
  disjoint P x
  disjoint P y
  disjoint F s
  disjoint F t
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint K y
  disjoint N j
  disjoint N w
  disjoint ph r
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint R w
  disjoint U w
  disjoint X r
  disjoint X w
  disjoint Y j
  disjoint Y r
  disjoint Y s
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y z
  disjoint D r
  disjoint D s
  disjoint D t
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D z
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S z
  disjoint T r
  disjoint T y
  disjoint L y
  assert |- ( ph -> E! x e. Y A. y e. Y ( N ` ( A .- x ) ) <_ ( N ` ( A .- y ) ) )

  proof
    wph
    cA
    vx
    cv
    #
    c.mi
    co
    #
    cN
    cfv
    #
    cA
    vy
    cv
    c.mi
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
    c.mi
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
    c.mi
    cN
    cX
    cY
    minvec.x
    minvec.m
    minvec.n
    minvec.u
    minvec.y
    minvec.w
    minvec.a
    minvec.j
    minvec.r
    minvec.s
    minvec.d
    minveclem5
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
    c.mi
    cN
    cX
    cY
    minvec.x
    minvec.m
    minvec.n
    wph
    cU
    ccph
    wcel
    #
    @16
    @21
    minvec.u
    ad2antrr
    wph
    cY
    cU
    clss
    cfv
    #
    wcel
    #
    @16
    @21
    minvec.y
    ad2antrr
    wph
    cU
    cY
    cress
    co
    ccms
    wcel
    @16
    @21
    minvec.w
    ad2antrr
    wph
    cA
    cX
    wcel
    @16
    @21
    minvec.a
    ad2antrr
    minvec.j
    minvec.r
    minvec.s
    minvec.d
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
    minveclem2
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
    c.mi
    cN
    cX
    cY
    minvec.x
    minvec.m
    minvec.n
    minvec.u
    minvec.y
    minvec.w
    minvec.a
    minvec.j
    minvec.r
    minvec.s
    minvec.d
    minveclem6
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
    c.mi
    cN
    cX
    cY
    minvec.x
    minvec.m
    minvec.n
    minvec.u
    minvec.y
    minvec.w
    minvec.a
    minvec.j
    minvec.r
    minvec.s
    minvec.d
    minveclem6
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
    cmt
    wcel
    #
    @35
    wph
    @38
    @16
    wph
    @27
    cU
    cngp
    wcel
    @38
    minvec.u
    cU
    cphngp
    cU
    ngpms
    3syl
    adantr
    cD
    cU
    cX
    minvec.x
    minvec.d
    msmet
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
    @29
    @40
    minvec.y
    @28
    cY
    cX
    cU
    minvec.x
    @28
    eqid
    lssss
    syl
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
    @41
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
    @44
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
    @45
    wb
    @17
    @22
    @44
    recnd
    @22
    sqeq0
    syl
    @17
    @35
    @36
    @37
    @45
    @12
    wb
    @39
    @42
    @43
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
    c.mi
    oveq2
    fveq2d
    breq1d
    ralbidv
    reu4
    sylanbrc
end
