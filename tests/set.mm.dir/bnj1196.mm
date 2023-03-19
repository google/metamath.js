include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "df-rex.mm"
include "sylib.mm"

theorem bnj1196
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume bnj1196.1: |- ( ph -> E. x e. A ps )


  assert |- ( ph -> E. x ( x e. A /\ ps ) )

  proof
    wph
    wps
    vx
    cA
    wrex
    vx
    cv
    cA
    wcel
    wps
    wa
    vx
    wex
    bnj1196.1
    wps
    vx
    cA
    df-rex
    sylib
end
