include "crab.mm"
include "wss.mm"
include "wi.mm"
include "ss2rab.mm"
include "mprgbir.mm"

theorem ss2rabi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume ss2rabi.1: |- ( x e. A -> ( ph -> ps ) )


  assert |- { x e. A | ph } C_ { x e. A | ps }

  proof
    wph
    vx
    cA
    crab
    wps
    vx
    cA
    crab
    wss
    wph
    wps
    wi
    vx
    cA
    wph
    wps
    vx
    cA
    ss2rab
    ss2rabi.1
    mprgbir
end
