include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "crab.mm"
include "cvv.mm"
include "cmpt.mm"
include "fsovfvd.mm"
include "syl5eq.mm"
include "wceq.mm"
include "eleq1.mm"
include "rabbidv.mm"
include "adantl.mm"
include "rabexg.mm"
include "syl.mm"
include "fvmptd.mm"

theorem fsovfvfvd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cO: class O
  let cV: class V
  let cW: class W
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  assume fsovd.fs: |- O = ( a e. _V , b e. _V |-> ( f e. ( ~P b ^m a ) |-> ( y e. b |-> { x e. a | y e. ( f ` x ) } ) ) )
  assume fsovd.a: |- ( ph -> A e. V )
  assume fsovd.b: |- ( ph -> B e. W )
  assume fsovfvd.g: |- G = ( A O B )
  assume fsovfvd.f: |- ( ph -> F e. ( ~P B ^m A ) )
  assume fsovfvfvd.h: |- H = ( G ` F )
  assume fsovfvfvd.y: |- ( ph -> Y e. B )

  disjoint A a
  disjoint A b
  disjoint A f
  disjoint A x
  disjoint A y
  disjoint a b
  disjoint a f
  disjoint a x
  disjoint a y
  disjoint b f
  disjoint b x
  disjoint b y
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint B a
  disjoint B b
  disjoint B f
  disjoint B y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint Y x
  disjoint Y y
  disjoint a ph
  disjoint b ph
  disjoint f ph
  disjoint ph y
  assert |- ( ph -> ( H ` Y ) = { x e. A | Y e. ( F ` x ) } )

  proof
    wph
    vy
    cY
    vy
    cv
    #
    vx
    cv
    cF
    cfv
    #
    wcel
    #
    vx
    cA
    crab
    #
    cY
    @1
    wcel
    #
    vx
    cA
    crab
    #
    cB
    cH
    cvv
    wph
    cH
    cF
    cG
    cfv
    vy
    cB
    @3
    cmpt
    fsovfvfvd.h
    wph
    vx
    vy
    cA
    cB
    vf
    cF
    cG
    cO
    cV
    cW
    va
    vb
    fsovd.fs
    fsovd.a
    fsovd.b
    fsovfvd.g
    fsovfvd.f
    fsovfvd
    syl5eq
    @0
    cY
    wceq
    #
    @3
    @5
    wceq
    wph
    @6
    @2
    @4
    vx
    cA
    @0
    cY
    @1
    eleq1
    rabbidv
    adantl
    fsovfvfvd.y
    wph
    cA
    cV
    wcel
    @5
    cvv
    wcel
    fsovd.a
    @4
    vx
    cA
    cV
    rabexg
    syl
    fvmptd
end
