include "eximii.mm"

theorem bnj101
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume bnj101.1: |- E. x ph
  assume bnj101.2: |- ( ph -> ps )


  assert |- E. x ps

  proof
    wph
    wps
    vx
    bnj101.1
    bnj101.2
    eximii
end
