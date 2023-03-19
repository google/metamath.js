include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "crab.mm"
include "cmpt.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "cvv.mm"
include "fsovd.mm"
include "syl5eq.mm"
include "wceq.mm"
include "fveq1.mm"
include "eleq2d.mm"
include "rabbidv.mm"
include "mpteq2dv.mm"
include "adantl.mm"
include "mptexg.mm"
include "syl.mm"
include "fvmptd.mm"

theorem fsovfvd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cO: class O
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume fsovd.fs: |- O = ( a e. _V , b e. _V |-> ( f e. ( ~P b ^m a ) |-> ( y e. b |-> { x e. a | y e. ( f ` x ) } ) ) )
  assume fsovd.a: |- ( ph -> A e. V )
  assume fsovd.b: |- ( ph -> B e. W )
  assume fsovfvd.g: |- G = ( A O B )
  assume fsovfvd.f: |- ( ph -> F e. ( ~P B ^m A ) )

  disjoint A a
  disjoint A b
  disjoint A f
  disjoint A x
  disjoint a b
  disjoint a f
  disjoint a x
  disjoint b f
  disjoint b x
  disjoint f x
  disjoint A y
  disjoint a y
  disjoint b y
  disjoint f y
  disjoint B a
  disjoint B b
  disjoint B f
  disjoint B y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint a ph
  disjoint b ph
  disjoint f ph
  assert |- ( ph -> ( G ` F ) = ( y e. B |-> { x e. A | y e. ( F ` x ) } ) )

  proof
    wph
    vf
    cF
    vy
    cB
    vy
    cv
    #
    vx
    cv
    #
    vf
    cv
    #
    cfv
    #
    wcel
    #
    vx
    cA
    crab
    #
    cmpt
    #
    vy
    cB
    @0
    @1
    cF
    cfv
    #
    wcel
    #
    vx
    cA
    crab
    #
    cmpt
    #
    cB
    cpw
    cA
    cmap
    co
    #
    cG
    cvv
    wph
    cG
    cA
    cB
    cO
    co
    vf
    @11
    @6
    cmpt
    fsovfvd.g
    wph
    vx
    vy
    cA
    cB
    vf
    cO
    cV
    cW
    va
    vb
    fsovd.fs
    fsovd.a
    fsovd.b
    fsovd
    syl5eq
    @2
    cF
    wceq
    #
    @6
    @10
    wceq
    wph
    @12
    vy
    cB
    @5
    @9
    @12
    @4
    @8
    vx
    cA
    @12
    @3
    @7
    @0
    @1
    @2
    cF
    fveq1
    eleq2d
    rabbidv
    mpteq2dv
    adantl
    fsovfvd.f
    wph
    cB
    cW
    wcel
    @10
    cvv
    wcel
    fsovd.b
    vy
    cB
    @9
    cW
    mptexg
    syl
    fvmptd
end
