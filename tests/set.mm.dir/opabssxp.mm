include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "cxp.mm"
include "simpl.mm"
include "ssopab2i.mm"
include "df-xp.mm"
include "sseqtr4i.mm"

theorem opabssxp
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- { <. x , y >. | ( ( x e. A /\ y e. B ) /\ ph ) } C_ ( A X. B )

  proof
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    wa
    #
    wph
    wa
    #
    vx
    vy
    copab
    @0
    vx
    vy
    copab
    cA
    cB
    cxp
    @1
    @0
    vx
    vy
    @0
    wph
    simpl
    ssopab2i
    vx
    vy
    cA
    cB
    df-xp
    sseqtr4i
end
