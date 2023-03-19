include "wrel.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "df-br.mm"
include "3bitr3g.mm"
include "eqrelrdv2.mm"
include "anabss5.mm"

theorem eqbrrdv2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume eqbrrdv2.1: |- ( ( ( Rel A /\ Rel B ) /\ ph ) -> ( x A y <-> x B y ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ( ( Rel A /\ Rel B ) /\ ph ) -> A = B )

  proof
    cA
    wrel
    cB
    wrel
    wa
    #
    wph
    cA
    cB
    wceq
    @0
    wph
    wa
    #
    vx
    vy
    cA
    cB
    @1
    vx
    cv
    #
    vy
    cv
    #
    cA
    wbr
    @2
    @3
    cB
    wbr
    @2
    @3
    cop
    #
    cA
    wcel
    @4
    cB
    wcel
    eqbrrdv2.1
    @2
    @3
    cA
    df-br
    @2
    @3
    cB
    df-br
    3bitr3g
    eqrelrdv2
    anabss5
end
