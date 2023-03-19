include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "rsp.mm"
include "imp.mm"

theorem rspa
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( ( A. x e. A ph /\ x e. A ) -> ph )

  proof
    wph
    vx
    cA
    wral
    vx
    cv
    cA
    wcel
    wph
    wph
    vx
    cA
    rsp
    imp
end
