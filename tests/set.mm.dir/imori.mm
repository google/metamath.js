include "wi.mm"
include "wn.mm"
include "wo.mm"
include "imor.mm"
include "mpbi.mm"

theorem imori
  let wph: wff ph
  let wps: wff ps
  assume imori.1: |- ( ph -> ps )


  assert |- ( -. ph \/ ps )

  proof
    wph
    wps
    wi
    wph
    wn
    wps
    wo
    imori.1
    wph
    wps
    imor
    mpbi
end
