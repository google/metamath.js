include "wrex.mm"
include "rexlimdvaa.mm"
include "mpd.mm"

theorem rexlimddv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rexlimddv.1: |- ( ph -> E. x e. A ps )
  assume rexlimddv.2: |- ( ( ph /\ ( x e. A /\ ps ) ) -> ch )

  disjoint ph x
  disjoint ch x
  assert |- ( ph -> ch )

  proof
    wph
    wps
    vx
    cA
    wrex
    wch
    rexlimddv.1
    wph
    wps
    wch
    vx
    cA
    rexlimddv.2
    rexlimdvaa
    mpd
end
