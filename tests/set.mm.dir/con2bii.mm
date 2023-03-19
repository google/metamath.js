include "wn.mm"
include "bicomi.mm"
include "con1bii.mm"

theorem con2bii
  param wph: wff ph
  param wps: wff ps
  assume con2bii.1: |- ( ph <-> -. ps )


  assert |- ( ps <-> -. ph )

  proof
    wph
    wn
    wps
    wps
    wph
    wph
    wps
    wn
    con2bii.1
    bicomi
    con1bii
    bicomi
end
