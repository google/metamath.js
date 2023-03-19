include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cec.mm"
include "cqs.mm"
include "cvv.mm"
include "wer.mm"
include "cbs.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "erex.mm"
include "sylc.mm"
include "quslem.mm"
include "cv.mm"
include "ercpbl.mm"
include "imasaddvallem.mm"
include "3ad2ant1.mm"
include "divsfval.mm"
include "oveq12d.mm"
include "3eqtr3d.mm"

theorem qusaddvallem
  let wph: wff ph
  let vx: setvar x
  let c.sm: class .~
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  assume qusaddf.u: |- ( ph -> U = ( R /s .~ ) )
  assume qusaddf.v: |- ( ph -> V = ( Base ` R ) )
  assume qusaddf.r: |- ( ph -> .~ Er V )
  assume qusaddf.z: |- ( ph -> R e. Z )
  assume qusaddf.e: |- ( ph -> ( ( a .~ p /\ b .~ q ) -> ( a .x. b ) .~ ( p .x. q ) ) )
  assume qusaddf.c: |- ( ( ph /\ ( p e. V /\ q e. V ) ) -> ( p .x. q ) e. V )
  assume qusaddflem.f: |- F = ( x e. V |-> [ x ] .~ )
  assume qusaddflem.g: |- ( ph -> .xb = U_ p e. V U_ q e. V { <. <. ( F ` p ) , ( F ` q ) >. , ( F ` ( p .x. q ) ) >. } )

  disjoint a b
  disjoint a p
  disjoint a q
  disjoint a x
  disjoint .~ a
  disjoint b p
  disjoint b q
  disjoint b x
  disjoint .~ b
  disjoint p q
  disjoint p x
  disjoint .~ p
  disjoint q x
  disjoint .~ q
  disjoint .~ x
  disjoint F a
  disjoint F b
  disjoint F p
  disjoint F q
  disjoint a ph
  disjoint b ph
  disjoint p ph
  disjoint ph q
  disjoint ph x
  disjoint V a
  disjoint V b
  disjoint V p
  disjoint V q
  disjoint V x
  disjoint R p
  disjoint R q
  disjoint R x
  disjoint .x. p
  disjoint .x. q
  disjoint .x. x
  disjoint X p
  disjoint X q
  disjoint X x
  disjoint .xb a
  disjoint .xb b
  disjoint .xb p
  disjoint .xb q
  disjoint Y p
  disjoint Y q
  disjoint Y x
  assert |- ( ( ph /\ X e. V /\ Y e. V ) -> ( [ X ] .~ .xb [ Y ] .~ ) = [ ( X .x. Y ) ] .~ )

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
    cX
    cY
    c.x
    co
    #
    cF
    cfv
    cX
    c.sm
    cec
    #
    cY
    c.sm
    cec
    #
    c.xb
    co
    @5
    c.sm
    cec
    wph
    cV
    c.sm
    cqs
    c.xb
    c.x
    cF
    cV
    cX
    cY
    vq
    vp
    va
    vb
    wph
    vx
    c.sm
    cR
    cU
    cF
    cV
    cvv
    cZ
    qusaddf.u
    qusaddf.v
    qusaddflem.f
    wph
    cV
    c.sm
    wer
    #
    cV
    cvv
    wcel
    #
    c.sm
    cvv
    wcel
    qusaddf.r
    wph
    cV
    cR
    cbs
    cfv
    cvv
    qusaddf.v
    cR
    cbs
    fvex
    syl6eqel
    #
    cV
    c.sm
    cvv
    erex
    sylc
    qusaddf.z
    quslem
    wph
    vx
    va
    cv
    vb
    cv
    vp
    cv
    vq
    cv
    c.x
    c.sm
    cF
    cV
    vp
    vq
    qusaddf.r
    @10
    qusaddflem.f
    qusaddf.c
    qusaddf.e
    ercpbl
    qusaddflem.g
    imasaddvallem
    @2
    @3
    @6
    @4
    @7
    c.xb
    @2
    vx
    cX
    c.sm
    cF
    cV
    wph
    @0
    @8
    @1
    qusaddf.r
    3ad2ant1
    #
    wph
    @0
    @9
    @1
    @10
    3ad2ant1
    #
    qusaddflem.f
    divsfval
    @2
    vx
    cY
    c.sm
    cF
    cV
    @11
    @12
    qusaddflem.f
    divsfval
    oveq12d
    @2
    vx
    @5
    c.sm
    cF
    cV
    @11
    @12
    qusaddflem.f
    divsfval
    3eqtr3d
end
