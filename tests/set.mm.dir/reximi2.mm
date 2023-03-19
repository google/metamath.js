include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "eximi.mm"
include "df-rex.mm"
include "3imtr4i.mm"

theorem reximi2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume reximi2.1: |- ( ( x e. A /\ ph ) -> ( x e. B /\ ps ) )


  assert |- ( E. x e. A ph -> E. x e. B ps )

  proof
    vx
    cv
    #
    cA
    wcel
    wph
    wa
    #
    vx
    wex
    @0
    cB
    wcel
    wps
    wa
    #
    vx
    wex
    wph
    vx
    cA
    wrex
    wps
    vx
    cB
    wrex
    @1
    @2
    vx
    reximi2.1
    eximi
    wph
    vx
    cA
    df-rex
    wps
    vx
    cB
    df-rex
    3imtr4i
end
