include "cab.mm"
include "wss.mm"
include "wi.mm"
include "ss2ab.mm"
include "mpgbir.mm"

theorem ss2abi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume ss2abi.1: |- ( ph -> ps )


  assert |- { x | ph } C_ { x | ps }

  proof
    wph
    vx
    cab
    wps
    vx
    cab
    wss
    wph
    wps
    wi
    vx
    wph
    wps
    vx
    ss2ab
    ss2abi.1
    mpgbir
end
