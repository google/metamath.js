include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "csn.mm"
include "cv.mm"
include "cmpt2.mm"
include "cop.mm"
include "wfun.mm"
include "wss.mm"
include "cdm.mm"
include "wceq.mm"
include "cxp.mm"
include "wfn.mm"
include "imasvscafn.mm"
include "fnfun.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "ciun.mm"
include "eqidd.mm"
include "fveq2.mm"
include "sneqd.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "mpt2eq123dv.mm"
include "ssiun2s.mm"
include "3ad2ant3.mm"
include "imasvsca.mm"
include "sseqtr4d.mm"
include "simp2.mm"
include "fvex.mm"
include "snid.mm"
include "opelxpi.mm"
include "sylancl.mm"
include "eqid.mm"
include "dmmpt2.mm"
include "syl6eleqr.mm"
include "funssfv.mm"
include "syl3anc.mm"
include "df-ov.mm"
include "3eqtr4g.mm"
include "oveq1.mm"
include "ovmpt2.mm"
include "eqtrd.mm"

theorem imasvscaval
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume imasvscaf.u: |- ( ph -> U = ( F "s R ) )
  assume imasvscaf.v: |- ( ph -> V = ( Base ` R ) )
  assume imasvscaf.f: |- ( ph -> F : V -onto-> B )
  assume imasvscaf.r: |- ( ph -> R e. Z )
  assume imasvscaf.g: |- G = ( Scalar ` R )
  assume imasvscaf.k: |- K = ( Base ` G )
  assume imasvscaf.q: |- .x. = ( .s ` R )
  assume imasvscaf.s: |- .xb = ( .s ` U )
  assume imasvscaf.e: |- ( ( ph /\ ( p e. K /\ a e. V /\ q e. V ) ) -> ( ( F ` a ) = ( F ` q ) -> ( F ` ( p .x. a ) ) = ( F ` ( p .x. q ) ) ) )

  disjoint a p
  disjoint a q
  disjoint F a
  disjoint p q
  disjoint F p
  disjoint F q
  disjoint K a
  disjoint K p
  disjoint K q
  disjoint a ph
  disjoint p ph
  disjoint ph q
  disjoint B p
  disjoint B q
  disjoint R p
  disjoint R q
  disjoint .x. p
  disjoint .x. q
  disjoint .xb a
  disjoint .xb p
  disjoint .xb q
  disjoint V a
  disjoint V p
  disjoint V q
  disjoint X p
  disjoint Y p
  disjoint Y q
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint ph w
  disjoint ph x
  disjoint U x
  disjoint B x
  disjoint R x
  disjoint .x. w
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint .xb w
  disjoint .xb x
  disjoint .xb y
  disjoint V w
  disjoint V x
  disjoint V y
  disjoint X x
  disjoint Y x
  assert |- ( ( ph /\ X e. K /\ Y e. V ) -> ( X .xb ( F ` Y ) ) = ( F ` ( X .x. Y ) ) )

  proof
    wph
    cX
    cK
    wcel
    #
    cY
    cV
    wcel
    #
    w3a
    #
    cX
    cY
    cF
    cfv
    #
    c.xb
    co
    #
    cX
    @3
    vp
    vx
    cK
    @3
    csn
    #
    vp
    cv
    #
    cY
    c.x
    co
    #
    cF
    cfv
    #
    cmpt2
    #
    co
    #
    cX
    cY
    c.x
    co
    #
    cF
    cfv
    #
    @2
    cX
    @3
    cop
    #
    c.xb
    cfv
    #
    @13
    @9
    cfv
    #
    @4
    @10
    @2
    c.xb
    wfun
    #
    @9
    c.xb
    wss
    @13
    @9
    cdm
    #
    wcel
    @14
    @15
    wceq
    wph
    @0
    @16
    @1
    wph
    c.xb
    cK
    cB
    cxp
    #
    wfn
    @16
    wph
    cB
    cR
    c.xb
    c.x
    cU
    cF
    cG
    cK
    cV
    cZ
    vq
    vp
    va
    imasvscaf.u
    imasvscaf.v
    imasvscaf.f
    imasvscaf.r
    imasvscaf.g
    imasvscaf.k
    imasvscaf.q
    imasvscaf.s
    imasvscaf.e
    imasvscafn
    @18
    c.xb
    fnfun
    syl
    3ad2ant1
    @2
    @9
    vq
    cV
    vp
    vx
    cK
    vq
    cv
    #
    cF
    cfv
    #
    csn
    #
    @6
    @19
    c.x
    co
    #
    cF
    cfv
    #
    cmpt2
    #
    ciun
    #
    c.xb
    @1
    wph
    @9
    @25
    wss
    @0
    vq
    cV
    @24
    cY
    @9
    @19
    cY
    wceq
    #
    vp
    vx
    cK
    @21
    @23
    cK
    @5
    @8
    @26
    cK
    eqidd
    @26
    @20
    @3
    @19
    cY
    cF
    fveq2
    sneqd
    @26
    @22
    @7
    cF
    @19
    cY
    @6
    c.x
    oveq2
    fveq2d
    mpt2eq123dv
    ssiun2s
    3ad2ant3
    wph
    @0
    c.xb
    @25
    wceq
    @1
    wph
    vx
    cB
    cR
    c.xb
    c.x
    cU
    cF
    cG
    cK
    cV
    cZ
    vq
    vp
    imasvscaf.u
    imasvscaf.v
    imasvscaf.f
    imasvscaf.r
    imasvscaf.g
    imasvscaf.k
    imasvscaf.q
    imasvscaf.s
    imasvsca
    3ad2ant1
    sseqtr4d
    @2
    @13
    cK
    @5
    cxp
    #
    @17
    @2
    @0
    @3
    @5
    wcel
    #
    @13
    @27
    wcel
    wph
    @0
    @1
    simp2
    #
    @3
    cY
    cF
    fvex
    snid
    #
    cX
    @3
    cK
    @5
    opelxpi
    sylancl
    vp
    vx
    cK
    @5
    @8
    @9
    @9
    eqid
    #
    @7
    cF
    fvex
    dmmpt2
    syl6eleqr
    @13
    c.xb
    @9
    funssfv
    syl3anc
    cX
    @3
    c.xb
    df-ov
    cX
    @3
    @9
    df-ov
    3eqtr4g
    @2
    @0
    @28
    @10
    @12
    wceq
    @29
    @30
    vp
    vx
    cX
    @3
    cK
    @5
    @8
    @12
    @9
    @12
    @6
    cX
    wceq
    @7
    @11
    cF
    @6
    cX
    cY
    c.x
    oveq1
    fveq2d
    vx
    cv
    @3
    wceq
    @12
    eqidd
    @31
    @11
    cF
    fvex
    ovmpt2
    sylancl
    eqtrd
end
