include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "chil.mm"
include "wss.mm"
include "wi.mm"
include "ax-1.mm"
include "helch.mm"
include "stcltr1i.mm"
include "syl5.mm"
include "chssii.mm"
include "eqss.mm"
include "mpbiran.mm"
include "syl6ibr.mm"

theorem stcltr2i
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cS: class S
  let cB: class B
  assume stcltr1.1: |- ( ph <-> ( S e. States /\ A. x e. CH A. y e. CH ( ( ( S ` x ) = 1 -> ( S ` y ) = 1 ) -> x C_ y ) ) )
  assume stcltr1.2: |- A e. CH

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint S x
  disjoint S y
  disjoint B x
  disjoint B y
  assert |- ( ph -> ( ( S ` A ) = 1 -> A = ~H ) )

  proof
    wph
    cA
    cS
    cfv
    c1
    wceq
    #
    chil
    cA
    wss
    #
    cA
    chil
    wceq
    #
    @0
    chil
    cS
    cfv
    c1
    wceq
    #
    @0
    wi
    wph
    @1
    @0
    @3
    ax-1
    wph
    vx
    vy
    chil
    cA
    cS
    stcltr1.1
    helch
    stcltr1.2
    stcltr1i
    syl5
    @2
    cA
    chil
    wss
    @1
    cA
    stcltr1.2
    chssii
    cA
    chil
    eqss
    mpbiran
    syl6ibr
end
