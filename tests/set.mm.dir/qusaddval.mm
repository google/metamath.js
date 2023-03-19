include "cv.mm"
include "cec.mm"
include "cmpt.mm"
include "eqid.mm"
include "cqs.mm"
include "cvv.mm"
include "wer.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "erex.mm"
include "sylc.mm"
include "qusval.mm"
include "quslem.mm"
include "imasplusg.mm"
include "qusaddvallem.mm"

theorem qusaddval
  let wph: wff ph
  let c.sm: class .~
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let cF: class F
  assume qusaddf.u: |- ( ph -> U = ( R /s .~ ) )
  assume qusaddf.v: |- ( ph -> V = ( Base ` R ) )
  assume qusaddf.r: |- ( ph -> .~ Er V )
  assume qusaddf.z: |- ( ph -> R e. Z )
  assume qusaddf.e: |- ( ph -> ( ( a .~ p /\ b .~ q ) -> ( a .x. b ) .~ ( p .x. q ) ) )
  assume qusaddf.c: |- ( ( ph /\ ( p e. V /\ q e. V ) ) -> ( p .x. q ) e. V )
  assume qusaddf.p: |- .x. = ( +g ` R )
  assume qusaddf.a: |- .xb = ( +g ` U )

  disjoint a b
  disjoint a p
  disjoint a q
  disjoint .~ a
  disjoint b p
  disjoint b q
  disjoint .~ b
  disjoint p q
  disjoint .~ p
  disjoint .~ q
  disjoint a ph
  disjoint b ph
  disjoint p ph
  disjoint ph q
  disjoint V a
  disjoint V b
  disjoint V p
  disjoint V q
  disjoint R p
  disjoint R q
  disjoint .x. p
  disjoint .x. q
  disjoint X p
  disjoint X q
  disjoint .xb a
  disjoint .xb b
  disjoint .xb p
  disjoint .xb q
  disjoint Y p
  disjoint Y q
  disjoint a x
  disjoint b x
  disjoint p x
  disjoint q x
  disjoint .~ x
  disjoint F a
  disjoint F b
  disjoint F p
  disjoint F q
  disjoint ph x
  disjoint V x
  disjoint R x
  disjoint .x. x
  disjoint X x
  disjoint Y x
  assert |- ( ( ph /\ X e. V /\ Y e. V ) -> ( [ X ] .~ .xb [ Y ] .~ ) = [ ( X .x. Y ) ] .~ )

  proof
    wph
    vx
    c.sm
    cR
    c.xb
    c.x
    cU
    vx
    cV
    vx
    cv
    c.sm
    cec
    cmpt
    #
    cV
    cX
    cY
    cZ
    vq
    vp
    va
    vb
    qusaddf.u
    qusaddf.v
    qusaddf.r
    qusaddf.z
    qusaddf.e
    qusaddf.c
    @0
    eqid
    #
    wph
    cV
    c.sm
    cqs
    c.x
    c.xb
    cR
    cU
    @0
    cV
    cZ
    vq
    vp
    wph
    vx
    c.sm
    cR
    cU
    @0
    cV
    cvv
    cZ
    qusaddf.u
    qusaddf.v
    @1
    wph
    cV
    c.sm
    wer
    cV
    cvv
    wcel
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
    cV
    c.sm
    cvv
    erex
    sylc
    #
    qusaddf.z
    qusval
    qusaddf.v
    wph
    vx
    c.sm
    cR
    cU
    @0
    cV
    cvv
    cZ
    qusaddf.u
    qusaddf.v
    @1
    @2
    qusaddf.z
    quslem
    qusaddf.z
    qusaddf.p
    qusaddf.a
    imasplusg
    qusaddvallem
end
