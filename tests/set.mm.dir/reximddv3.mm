include "cv.mm"
include "wcel.mm"
include "anasss.mm"
include "reximddv.mm"

theorem reximddv3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume reximddv3.1: |- ( ( ( ph /\ x e. A ) /\ ps ) -> ch )
  assume reximddv3.2: |- ( ph -> E. x e. A ps )

  disjoint ph x
  assert |- ( ph -> E. x e. A ch )

  proof
    wph
    wps
    wch
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    wps
    wch
    reximddv3.1
    anasss
    reximddv3.2
    reximddv
end
