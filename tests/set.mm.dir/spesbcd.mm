include "wsbc.mm"
include "wex.mm"
include "spesbc.mm"
include "syl.mm"

theorem spesbcd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let cB: class B
  assume spesbcd.1: |- ( ph -> [. A / x ]. ps )


  assert |- ( ph -> E. x ps )

  proof
    wph
    wps
    vx
    cA
    wsbc
    wps
    vx
    wex
    spesbcd.1
    wps
    vx
    cA
    spesbc
    syl
end
