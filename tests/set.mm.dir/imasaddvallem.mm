include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cop.mm"
include "df-ov.mm"
include "wfun.mm"
include "wceq.mm"
include "cxp.mm"
include "wfn.mm"
include "imasaddfnlem.mm"
include "fnfun.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "csn.mm"
include "wss.mm"
include "cv.mm"
include "ciun.mm"
include "fveq2.mm"
include "opeq1d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "opeq12d.mm"
include "sneqd.mm"
include "ssiun2s.mm"
include "3ad2ant2.mm"
include "wral.mm"
include "opeq2d.mm"
include "oveq2.mm"
include "ralrimivw.mm"
include "ss2iun.mm"
include "3ad2ant3.mm"
include "sstrd.mm"
include "sseqtr4d.mm"
include "opex.mm"
include "snss.mm"
include "sylibr.mm"
include "funopfv.mm"
include "sylc.mm"
include "syl5eq.mm"

theorem imasaddvallem
  let wph: wff ph
  let cB: class B
  let c.xb: class .xb
  let c.x: class .x.
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let cR: class R
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  assume imasaddf.f: |- ( ph -> F : V -onto-> B )
  assume imasaddf.e: |- ( ( ph /\ ( a e. V /\ b e. V ) /\ ( p e. V /\ q e. V ) ) -> ( ( ( F ` a ) = ( F ` p ) /\ ( F ` b ) = ( F ` q ) ) -> ( F ` ( a .x. b ) ) = ( F ` ( p .x. q ) ) ) )
  assume imasaddflem.a: |- ( ph -> .xb = U_ p e. V U_ q e. V { <. <. ( F ` p ) , ( F ` q ) >. , ( F ` ( p .x. q ) ) >. } )

  disjoint p q
  disjoint B p
  disjoint B q
  disjoint a b
  disjoint a p
  disjoint a q
  disjoint V a
  disjoint b p
  disjoint b q
  disjoint V b
  disjoint V p
  disjoint V q
  disjoint .x. p
  disjoint .x. q
  disjoint X p
  disjoint F a
  disjoint F b
  disjoint F p
  disjoint F q
  disjoint a ph
  disjoint b ph
  disjoint p ph
  disjoint ph q
  disjoint .xb a
  disjoint .xb b
  disjoint .xb p
  disjoint .xb q
  disjoint Y p
  disjoint Y q
  disjoint R p
  disjoint R q
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint b w
  disjoint b y
  disjoint b z
  disjoint p w
  disjoint p y
  disjoint p z
  disjoint q w
  disjoint q y
  disjoint q z
  disjoint w y
  disjoint w z
  disjoint V w
  disjoint y z
  disjoint V y
  disjoint V z
  disjoint .x. w
  disjoint a x
  disjoint b x
  disjoint p x
  disjoint q x
  disjoint w x
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint ph w
  disjoint .xb w
  disjoint .xb x
  disjoint .xb y
  disjoint .xb z
  assert |- ( ( ph /\ X e. V /\ Y e. V ) -> ( ( F ` X ) .xb ( F ` Y ) ) = ( F ` ( X .x. Y ) ) )

  proof
    wph
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    w3a
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    c.xb
    co
    @3
    @4
    cop
    #
    c.xb
    cfv
    #
    cX
    cY
    c.x
    co
    #
    cF
    cfv
    #
    @3
    @4
    c.xb
    df-ov
    @2
    c.xb
    wfun
    #
    @5
    @8
    cop
    #
    c.xb
    wcel
    #
    @6
    @8
    wceq
    wph
    @0
    @9
    @1
    wph
    c.xb
    cB
    cB
    cxp
    #
    wfn
    @9
    wph
    cB
    c.xb
    c.x
    cF
    cV
    vq
    vp
    va
    vb
    imasaddf.f
    imasaddf.e
    imasaddflem.a
    imasaddfnlem
    @12
    c.xb
    fnfun
    syl
    3ad2ant1
    @2
    @10
    csn
    #
    c.xb
    wss
    @11
    @2
    @13
    vp
    cV
    vq
    cV
    vp
    cv
    #
    cF
    cfv
    #
    vq
    cv
    #
    cF
    cfv
    #
    cop
    #
    @14
    @16
    c.x
    co
    #
    cF
    cfv
    #
    cop
    #
    csn
    #
    ciun
    #
    ciun
    #
    c.xb
    @2
    @13
    vp
    cV
    @15
    @4
    cop
    #
    @14
    cY
    c.x
    co
    #
    cF
    cfv
    #
    cop
    #
    csn
    #
    ciun
    #
    @24
    @0
    wph
    @13
    @30
    wss
    @1
    vp
    cV
    @29
    cX
    @13
    @14
    cX
    wceq
    #
    @28
    @10
    @31
    @25
    @5
    @27
    @8
    @31
    @15
    @3
    @4
    @14
    cX
    cF
    fveq2
    opeq1d
    @31
    @26
    @7
    cF
    @14
    cX
    cY
    c.x
    oveq1
    fveq2d
    opeq12d
    sneqd
    ssiun2s
    3ad2ant2
    @1
    wph
    @30
    @24
    wss
    #
    @0
    @1
    @29
    @23
    wss
    #
    vp
    cV
    wral
    @32
    @1
    @33
    vp
    cV
    vq
    cV
    @22
    cY
    @29
    @16
    cY
    wceq
    #
    @21
    @28
    @34
    @18
    @25
    @20
    @27
    @34
    @17
    @4
    @15
    @16
    cY
    cF
    fveq2
    opeq2d
    @34
    @19
    @26
    cF
    @16
    cY
    @14
    c.x
    oveq2
    fveq2d
    opeq12d
    sneqd
    ssiun2s
    ralrimivw
    vp
    cV
    @29
    @23
    ss2iun
    syl
    3ad2ant3
    sstrd
    wph
    @0
    c.xb
    @24
    wceq
    @1
    imasaddflem.a
    3ad2ant1
    sseqtr4d
    @10
    c.xb
    @5
    @8
    opex
    snss
    sylibr
    @5
    @8
    c.xb
    funopfv
    sylc
    syl5eq
end
