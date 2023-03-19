include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "wa.mm"
include "rspe.mm"
include "sylan2.mm"
include "3impb.mm"

theorem rsp2e
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B


  assert |- ( ( x e. A /\ y e. B /\ ph ) -> E. x e. A E. y e. B ph )

  proof
    vx
    cv
    cA
    wcel
    #
    vy
    cv
    cB
    wcel
    #
    wph
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    #
    @1
    wph
    wa
    @0
    @2
    @3
    wph
    vy
    cB
    rspe
    @2
    vx
    cA
    rspe
    sylan2
    3impb
end
