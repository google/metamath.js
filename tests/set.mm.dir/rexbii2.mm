include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "exbii.mm"
include "df-rex.mm"
include "3bitr4i.mm"

theorem rexbii2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rexbii2.1: |- ( ( x e. A /\ ph ) <-> ( x e. B /\ ps ) )


  assert |- ( E. x e. A ph <-> E. x e. B ps )

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
    rexbii2.1
    exbii
    wph
    vx
    cA
    df-rex
    wps
    vx
    cB
    df-rex
    3bitr4i
end
