include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cmpt.mm"
include "cxp.mm"
include "cpw.mm"
include "cvv.mm"
include "co.mm"
include "rfovd.mm"
include "syl5eq.mm"
include "wceq.mm"
include "breq.mm"
include "rabbidv.mm"
include "mpteq2dv.mm"
include "adantl.mm"
include "wcel.mm"
include "mptexg.mm"
include "syl.mm"
include "fvmptd.mm"

theorem rfovfvd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cO: class O
  let cV: class V
  let cW: class W
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  assume rfovd.rf: |- O = ( a e. _V , b e. _V |-> ( r e. ~P ( a X. b ) |-> ( x e. a |-> { y e. b | x r y } ) ) )
  assume rfovd.a: |- ( ph -> A e. V )
  assume rfovd.b: |- ( ph -> B e. W )
  assume rfovfvd.r: |- ( ph -> R e. ~P ( A X. B ) )
  assume rfovfvd.f: |- F = ( A O B )

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
  disjoint R r
  disjoint R x
  disjoint R y
  disjoint a ph
  disjoint b ph
  disjoint ph r
  assert |- ( ph -> ( F ` R ) = ( x e. A |-> { y e. B | x R y } ) )

  proof
    wph
    vr
    cR
    vx
    cA
    vx
    cv
    #
    vy
    cv
    #
    vr
    cv
    #
    wbr
    #
    vy
    cB
    crab
    #
    cmpt
    #
    vx
    cA
    @0
    @1
    cR
    wbr
    #
    vy
    cB
    crab
    #
    cmpt
    #
    cA
    cB
    cxp
    cpw
    #
    cF
    cvv
    wph
    cF
    cA
    cB
    cO
    co
    vr
    @9
    @5
    cmpt
    rfovfvd.f
    wph
    vx
    vy
    cA
    cB
    cO
    cV
    cW
    vr
    va
    vb
    rfovd.rf
    rfovd.a
    rfovd.b
    rfovd
    syl5eq
    @2
    cR
    wceq
    #
    @5
    @8
    wceq
    wph
    @10
    vx
    cA
    @4
    @7
    @10
    @3
    @6
    vy
    cB
    @0
    @1
    @2
    cR
    breq
    rabbidv
    mpteq2dv
    adantl
    rfovfvd.r
    wph
    cA
    cV
    wcel
    @8
    cvv
    wcel
    rfovd.a
    vx
    cA
    @7
    cV
    mptexg
    syl
    fvmptd
end
