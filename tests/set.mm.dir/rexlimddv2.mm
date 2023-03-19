include "cv.mm"
include "wcel.mm"
include "anasss.mm"
include "rexlimddv.mm"

theorem rexlimddv2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let vk: setvar k
  assume rexlimddv2.1: |- ( ph -> E. x e. A ps )
  assume rexlimddv2.2: |- ( ( ( ph /\ x e. A ) /\ ps ) -> ch )

  disjoint ch x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    vx
    cA
    rexlimddv2.1
    wph
    vx
    cv
    cA
    wcel
    wps
    wch
    rexlimddv2.2
    anasss
    rexlimddv
end
