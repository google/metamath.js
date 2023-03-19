include "cvv.mm"
include "cv.mm"
include "cxp.mm"
include "cpw.mm"
include "wbr.mm"
include "crab.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "wceq.mm"
include "a1i.mm"
include "wa.mm"
include "xpeq12.mm"
include "pweqd.mm"
include "simpl.mm"
include "rabeq.mm"
include "adantl.mm"
include "mpteq12dv.mm"
include "elexd.mm"
include "wcel.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "pwexg.mm"
include "mptexg.mm"
include "3syl.mm"
include "ovmpt2d.mm"

theorem rfovd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cO: class O
  let cV: class V
  let cW: class W
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  assume rfovd.rf: |- O = ( a e. _V , b e. _V |-> ( r e. ~P ( a X. b ) |-> ( x e. a |-> { y e. b | x r y } ) ) )
  assume rfovd.a: |- ( ph -> A e. V )
  assume rfovd.b: |- ( ph -> B e. W )

  disjoint A a
  disjoint A b
  disjoint A r
  disjoint a b
  disjoint a r
  disjoint b r
  disjoint A x
  disjoint a x
  disjoint b x
  disjoint B a
  disjoint B b
  disjoint B r
  disjoint B x
  disjoint B y
  disjoint a y
  disjoint b y
  disjoint a ph
  disjoint b ph
  assert |- ( ph -> ( A O B ) = ( r e. ~P ( A X. B ) |-> ( x e. A |-> { y e. B | x r y } ) ) )

  proof
    wph
    va
    vb
    cA
    cB
    cvv
    cvv
    vr
    va
    cv
    #
    vb
    cv
    #
    cxp
    #
    cpw
    #
    vx
    @0
    vx
    cv
    vy
    cv
    vr
    cv
    wbr
    #
    vy
    @1
    crab
    #
    cmpt
    #
    cmpt
    #
    vr
    cA
    cB
    cxp
    #
    cpw
    #
    vx
    cA
    @4
    vy
    cB
    crab
    #
    cmpt
    #
    cmpt
    #
    cO
    cvv
    cO
    va
    vb
    cvv
    cvv
    @7
    cmpt2
    wceq
    wph
    rfovd.rf
    a1i
    @0
    cA
    wceq
    #
    @1
    cB
    wceq
    #
    wa
    #
    @7
    @12
    wceq
    wph
    @15
    vr
    @3
    @6
    @9
    @11
    @15
    @2
    @8
    @0
    cA
    @1
    cB
    xpeq12
    pweqd
    @15
    vx
    @0
    @5
    cA
    @10
    @13
    @14
    simpl
    @14
    @5
    @10
    wceq
    @13
    @4
    vy
    @1
    cB
    rabeq
    adantl
    mpteq12dv
    mpteq12dv
    adantl
    wph
    cA
    cV
    rfovd.a
    elexd
    wph
    cB
    cW
    rfovd.b
    elexd
    wph
    @8
    cvv
    wcel
    #
    @9
    cvv
    wcel
    @12
    cvv
    wcel
    wph
    cA
    cV
    wcel
    cB
    cW
    wcel
    @16
    rfovd.a
    rfovd.b
    cA
    cB
    cV
    cW
    xpexg
    syl2anc
    @8
    cvv
    pwexg
    vr
    @9
    @11
    cvv
    mptexg
    3syl
    ovmpt2d
end
