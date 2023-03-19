include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "3exp.mm"
include "reximdai.mm"
include "mpd.mm"

theorem reximdd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume reximdd.1: |- F/ x ph
  assume reximdd.2: |- ( ( ph /\ x e. A /\ ps ) -> ch )
  assume reximdd.3: |- ( ph -> E. x e. A ps )


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
    reximdd.3
    wph
    wps
    wch
    vx
    cA
    reximdd.1
    wph
    vx
    cv
    cA
    wcel
    wps
    wch
    reximdd.2
    3exp
    reximdai
    mpd
end
