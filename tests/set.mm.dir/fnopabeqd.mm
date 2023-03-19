include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "opabbidv.mm"

theorem fnopabeqd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume fnopabeqd.1: |- ( ph -> B = C )

  disjoint ph x
  disjoint ph y
  assert |- ( ph -> { <. x , y >. | ( x e. A /\ y = B ) } = { <. x , y >. | ( x e. A /\ y = C ) } )

  proof
    wph
    vx
    cv
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wceq
    #
    wa
    @0
    @1
    cC
    wceq
    #
    wa
    vx
    vy
    wph
    @2
    @3
    @0
    wph
    cB
    cC
    @1
    fnopabeqd.1
    eqeq2d
    anbi2d
    opabbidv
end
