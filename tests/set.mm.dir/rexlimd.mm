include "wnf.mm"
include "a1i.mm"
include "rexlimd2.mm"

theorem rexlimd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rexlimd.1: |- F/ x ph
  assume rexlimd.2: |- F/ x ch
  assume rexlimd.3: |- ( ph -> ( x e. A -> ( ps -> ch ) ) )


  assert |- ( ph -> ( E. x e. A ps -> ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    rexlimd.1
    wch
    vx
    wnf
    wph
    rexlimd.2
    a1i
    rexlimd.3
    rexlimd2
end
