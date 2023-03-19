include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "cabs.mm"
include "cc.mm"
include "cclm.mm"
include "wcel.mm"
include "wss.mm"
include "tchclm.mm"
include "clmsscn.mm"
include "syl.mm"
include "sseldd.mm"
include "cjmulrcld.mm"
include "cjmulge0d.mm"
include "cr.mm"
include "tchcphlem3.mm"
include "mpdan.mm"
include "cc0.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "oveq12.mm"
include "anidms.mm"
include "breq2d.mm"
include "rspcv.mm"
include "sylc.mm"
include "sqrtmuld.mm"
include "cstv.mm"
include "cmulr.mm"
include "cphl.mm"
include "clmod.mm"
include "phllmod.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "ipassr.mm"
include "syl13anc.mm"
include "clmmul.mm"
include "oveqd.mm"
include "ipass.mm"
include "eqtr4d.mm"
include "clmcj.mm"
include "fveq1d.mm"
include "oveq123d.mm"
include "recnd.mm"
include "cjcld.mm"
include "mul32d.mm"
include "3eqtr2d.mm"
include "fveq2d.mm"
include "absval.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"

theorem tchcphlem2
  let wph: wff ph
  let vx: setvar x
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let c.xi: class .,
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.mi: class .-
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  assume tchval.n: |- G = ( toCHil ` W )
  assume tchcph.v: |- V = ( Base ` W )
  assume tchcph.f: |- F = ( Scalar ` W )
  assume tchcph.1: |- ( ph -> W e. PreHil )
  assume tchcph.2: |- ( ph -> F = ( CCfld |`s K ) )
  assume tchcph.h: |- ., = ( .i ` W )
  assume tchcph.3: |- ( ( ph /\ ( x e. K /\ x e. RR /\ 0 <_ x ) ) -> ( sqrt ` x ) e. K )
  assume tchcph.4: |- ( ( ph /\ x e. V ) -> 0 <_ ( x ., x ) )
  assume tchcph.k: |- K = ( Base ` F )
  assume tchcph.s: |- .x. = ( .s ` W )
  assume tchcphlem2.3: |- ( ph -> X e. K )
  assume tchcphlem2.4: |- ( ph -> Y e. V )

  disjoint ., x
  disjoint F x
  disjoint G x
  disjoint V x
  disjoint ph x
  disjoint W x
  disjoint .x. x
  disjoint X x
  disjoint Y x
  disjoint .- x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ., w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ., y
  disjoint ., z
  disjoint F y
  disjoint F z
  disjoint G y
  disjoint G z
  disjoint V w
  disjoint V y
  disjoint V z
  disjoint C x
  disjoint ph y
  disjoint ph z
  disjoint W w
  disjoint W y
  disjoint W z
  assert |- ( ph -> ( sqrt ` ( ( X .x. Y ) ., ( X .x. Y ) ) ) = ( ( abs ` X ) x. ( sqrt ` ( Y ., Y ) ) ) )

  proof
    wph
    cX
    cX
    ccj
    cfv
    #
    cmul
    co
    #
    cY
    cY
    c.xi
    co
    #
    cmul
    co
    #
    csqrt
    cfv
    @1
    csqrt
    cfv
    #
    @2
    csqrt
    cfv
    #
    cmul
    co
    cX
    cY
    c.x
    co
    #
    @6
    c.xi
    co
    #
    csqrt
    cfv
    cX
    cabs
    cfv
    #
    @5
    cmul
    co
    wph
    @1
    @2
    wph
    cX
    wph
    cK
    cc
    cX
    wph
    cW
    cclm
    wcel
    #
    cK
    cc
    wss
    wph
    cF
    cG
    cK
    cV
    cW
    tchval.n
    tchcph.v
    tchcph.f
    tchcph.1
    tchcph.2
    tchclm
    #
    cF
    cK
    cW
    tchcph.f
    tchcph.k
    clmsscn
    syl
    tchcphlem2.3
    sseldd
    #
    cjmulrcld
    wph
    cX
    @11
    cjmulge0d
    wph
    cY
    cV
    wcel
    #
    @2
    cr
    wcel
    tchcphlem2.4
    wph
    cF
    cG
    c.xi
    cK
    cV
    cW
    cY
    tchval.n
    tchcph.v
    tchcph.f
    tchcph.1
    tchcph.2
    tchcph.h
    tchcphlem3
    mpdan
    #
    wph
    @12
    cc0
    vx
    cv
    #
    @14
    c.xi
    co
    #
    cle
    wbr
    #
    vx
    cV
    wral
    cc0
    @2
    cle
    wbr
    #
    tchcphlem2.4
    wph
    @16
    vx
    cV
    tchcph.4
    ralrimiva
    @16
    @17
    vx
    cY
    cV
    @14
    cY
    wceq
    #
    @15
    @2
    cc0
    cle
    @18
    @15
    @2
    wceq
    @14
    cY
    @14
    cY
    c.xi
    oveq12
    anidms
    breq2d
    rspcv
    sylc
    sqrtmuld
    wph
    @7
    @3
    csqrt
    wph
    @7
    @6
    cY
    c.xi
    co
    #
    cX
    cF
    cstv
    cfv
    #
    cfv
    #
    cF
    cmulr
    cfv
    #
    co
    #
    cX
    @2
    cmul
    co
    #
    @0
    cmul
    co
    @3
    wph
    cW
    cphl
    wcel
    #
    @6
    cV
    wcel
    #
    @12
    cX
    cK
    wcel
    #
    @7
    @23
    wceq
    tchcph.1
    wph
    cW
    clmod
    wcel
    #
    @27
    @12
    @26
    wph
    @25
    @28
    tchcph.1
    cW
    phllmod
    syl
    tchcphlem2.3
    tchcphlem2.4
    cX
    c.x
    cF
    cK
    cV
    cW
    cY
    tchcph.v
    tchcph.f
    tchcph.s
    tchcph.k
    lmodvscl
    syl3anc
    tchcphlem2.4
    tchcphlem2.3
    @6
    cY
    cX
    c.x
    @22
    cF
    c.xi
    @20
    cK
    cV
    cW
    tchcph.f
    tchcph.h
    tchcph.v
    tchcph.k
    tchcph.s
    @22
    eqid
    #
    @20
    eqid
    ipassr
    syl13anc
    wph
    @24
    @19
    @0
    @21
    cmul
    @22
    wph
    @9
    cmul
    @22
    wceq
    @10
    cF
    cW
    tchcph.f
    clmmul
    syl
    #
    wph
    @24
    cX
    @2
    @22
    co
    #
    @19
    wph
    cmul
    @22
    cX
    @2
    @30
    oveqd
    wph
    @25
    @27
    @12
    @12
    @19
    @31
    wceq
    tchcph.1
    tchcphlem2.3
    tchcphlem2.4
    tchcphlem2.4
    cX
    cY
    cY
    c.x
    @22
    cF
    c.xi
    cK
    cV
    cW
    tchcph.f
    tchcph.h
    tchcph.v
    tchcph.k
    tchcph.s
    @29
    ipass
    syl13anc
    eqtr4d
    wph
    cX
    ccj
    @20
    wph
    @9
    ccj
    @20
    wceq
    @10
    cF
    cW
    tchcph.f
    clmcj
    syl
    fveq1d
    oveq123d
    wph
    cX
    @2
    @0
    @11
    wph
    @2
    @13
    recnd
    wph
    cX
    @11
    cjcld
    mul32d
    3eqtr2d
    fveq2d
    wph
    @8
    @4
    @5
    cmul
    wph
    cX
    cc
    wcel
    @8
    @4
    wceq
    @11
    cX
    absval
    syl
    oveq1d
    3eqtr4d
end
