include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "expr.mm"
include "reximdva.mm"
include "mpd.mm"

theorem reximddv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume reximddva.1: |- ( ( ph /\ ( x e. A /\ ps ) ) -> ch )
  assume reximddva.2: |- ( ph -> E. x e. A ps )

  disjoint ph x
  assert |- ( ph -> E. x e. A ch )

  proof
    wph
    wps
    vx
    cA
    wrex
    wch
    vx
    cA
    wrex
    reximddva.2
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
    reximddva.1
    expr
    reximdva
    mpd
end
