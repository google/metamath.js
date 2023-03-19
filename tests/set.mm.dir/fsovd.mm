include "cvv.mm"
include "cv.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "crab.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "wceq.mm"
include "a1i.mm"
include "wa.mm"
include "pweq.mm"
include "adantl.mm"
include "simpl.mm"
include "oveq12d.mm"
include "simpr.mm"
include "rabeq.mm"
include "adantr.mm"
include "mpteq12dv.mm"
include "elexd.mm"
include "ovex.mm"
include "mptex.mm"
include "ovmpt2d.mm"

theorem fsovd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cO: class O
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume fsovd.fs: |- O = ( a e. _V , b e. _V |-> ( f e. ( ~P b ^m a ) |-> ( y e. b |-> { x e. a | y e. ( f ` x ) } ) ) )
  assume fsovd.a: |- ( ph -> A e. V )
  assume fsovd.b: |- ( ph -> B e. W )

  disjoint A a
  disjoint A b
  disjoint A f
  disjoint a b
  disjoint a f
  disjoint b f
  disjoint A x
  disjoint a x
  disjoint b x
  disjoint A y
  disjoint a y
  disjoint b y
  disjoint B a
  disjoint B b
  disjoint B f
  disjoint B y
  disjoint a ph
  disjoint b ph
  assert |- ( ph -> ( A O B ) = ( f e. ( ~P B ^m A ) |-> ( y e. B |-> { x e. A | y e. ( f ` x ) } ) ) )

  proof
    wph
    va
    vb
    cA
    cB
    cvv
    cvv
    vf
    vb
    cv
    #
    cpw
    #
    va
    cv
    #
    cmap
    co
    #
    vy
    @0
    vy
    cv
    vx
    cv
    vf
    cv
    cfv
    wcel
    #
    vx
    @2
    crab
    #
    cmpt
    #
    cmpt
    #
    vf
    cB
    cpw
    #
    cA
    cmap
    co
    #
    vy
    cB
    @4
    vx
    cA
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
    fsovd.fs
    a1i
    @2
    cA
    wceq
    #
    @0
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
    vf
    @3
    @6
    @9
    @11
    @15
    @1
    @8
    @2
    cA
    cmap
    @14
    @1
    @8
    wceq
    @13
    @0
    cB
    pweq
    adantl
    @13
    @14
    simpl
    oveq12d
    @15
    vy
    @0
    @5
    cB
    @10
    @13
    @14
    simpr
    @13
    @5
    @10
    wceq
    @14
    @4
    vx
    @2
    cA
    rabeq
    adantr
    mpteq12dv
    mpteq12dv
    adantl
    wph
    cA
    cV
    fsovd.a
    elexd
    wph
    cB
    cW
    fsovd.b
    elexd
    @12
    cvv
    wcel
    wph
    vf
    @9
    @11
    @8
    cA
    cmap
    ovex
    mptex
    a1i
    ovmpt2d
end
