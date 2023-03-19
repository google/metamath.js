include "cv.mm"
include "cop.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "opelxp.mm"
include "anbi1i.mm"
include "oprabbii.mm"

theorem oprab4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- { <. <. x , y >. , z >. | ( <. x , y >. e. ( A X. B ) /\ ph ) } = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) }

  proof
    vx
    cv
    #
    vy
    cv
    #
    cop
    cA
    cB
    cxp
    wcel
    #
    wph
    wa
    @0
    cA
    wcel
    @1
    cB
    wcel
    wa
    #
    wph
    wa
    vx
    vy
    vz
    @2
    @3
    wph
    @0
    @1
    cA
    cB
    opelxp
    anbi1i
    oprabbii
end
