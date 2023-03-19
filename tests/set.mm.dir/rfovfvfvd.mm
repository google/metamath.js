include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cvv.mm"
include "cfv.mm"
include "cmpt.mm"
include "rfovfvd.mm"
include "syl5eq.mm"
include "wceq.mm"
include "breq1.mm"
include "rabbidv.mm"
include "adantl.mm"
include "wcel.mm"
include "rabexg.mm"
include "syl.mm"
include "fvmptd.mm"

theorem rfovfvfvd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cG: class G
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  assume rfovd.rf: |- O = ( a e. _V , b e. _V |-> ( r e. ~P ( a X. b ) |-> ( x e. a |-> { y e. b | x r y } ) ) )
  assume rfovd.a: |- ( ph -> A e. V )
  assume rfovd.b: |- ( ph -> B e. W )
  assume rfovfvd.r: |- ( ph -> R e. ~P ( A X. B ) )
  assume rfovfvd.f: |- F = ( A O B )
  assume rfovfvfvd.x: |- ( ph -> X e. A )
  assume rfovfvfvd.g: |- G = ( F ` R )

  disjoint A a
  disjoint A b
  disjoint A r
  disjoint A x
  disjoint a b
  disjoint a r
  disjoint a x
  disjoint b r
  disjoint b x
  disjoint r x
  disjoint B a
  disjoint B b
  disjoint B r
  disjoint B x
  disjoint B y
  disjoint a y
  disjoint b y
  disjoint r y
  disjoint x y
  disjoint R r
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint a ph
  disjoint b ph
  disjoint ph r
  disjoint ph x
  assert |- ( ph -> ( G ` X ) = { y e. B | X R y } )

  proof
    wph
    vx
    cX
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    vy
    cB
    crab
    #
    cX
    @1
    cR
    wbr
    #
    vy
    cB
    crab
    #
    cA
    cG
    cvv
    wph
    cG
    cR
    cF
    cfv
    vx
    cA
    @3
    cmpt
    rfovfvfvd.g
    wph
    vx
    vy
    cA
    cB
    cR
    cF
    cO
    cV
    cW
    vr
    va
    vb
    rfovd.rf
    rfovd.a
    rfovd.b
    rfovfvd.r
    rfovfvd.f
    rfovfvd
    syl5eq
    @0
    cX
    wceq
    #
    @3
    @5
    wceq
    wph
    @6
    @2
    @4
    vy
    cB
    @0
    cX
    @1
    cR
    breq1
    rabbidv
    adantl
    rfovfvfvd.x
    wph
    cB
    cW
    wcel
    @5
    cvv
    wcel
    rfovd.b
    @4
    vy
    cB
    cW
    rabexg
    syl
    fvmptd
end
