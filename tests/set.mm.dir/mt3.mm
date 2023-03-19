include "wn.mm"
include "mto.mm"
include "notnotri.mm"

theorem mt3
  let wph: wff ph
  let wps: wff ps
  assume mt3.1: |- -. ps
  assume mt3.2: |- ( -. ph -> ps )


  assert |- ph

  proof
    wph
    wph
    wn
    wps
    mt3.1
    mt3.2
    mto
    notnotri
end
