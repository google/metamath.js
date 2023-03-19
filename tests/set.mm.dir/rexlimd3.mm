include "cv.mm"
include "wcel.mm"
include "exp31.mm"
include "rexlimd.mm"

theorem rexlimd3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rexlimd3.1: |- F/ x ph
  assume rexlimd3.2: |- F/ x ch
  assume rexlimd3.3: |- ( ( ( ph /\ x e. A ) /\ ps ) -> ch )


  assert |- ( ph -> ( E. x e. A ps -> ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    rexlimd3.1
    rexlimd3.2
    wph
    vx
    cv
    cA
    wcel
    wps
    wch
    rexlimd3.3
    exp31
    rexlimd
end
