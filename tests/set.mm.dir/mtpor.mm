include "wn.mm"
include "ori.mm"
include "ax-mp.mm"

theorem mtpor
  let wph: wff ph
  let wps: wff ps
  assume mtpor.min: |- -. ph
  assume mtpor.max: |- ( ph \/ ps )


  assert |- ps

  proof
    wph
    wn
    wps
    mtpor.min
    wph
    wps
    mtpor.max
    ori
    ax-mp
end
