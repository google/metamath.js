include "wn.mm"
include "con1bii.mm"
include "bicomi.mm"

theorem con1bii2
  let wph: wff ph
  let wps: wff ps
  assume con1bii2.1: |- ( -. ph <-> ps )


  assert |- ( ph <-> -. ps )

  proof
    wps
    wn
    wph
    wph
    wps
    con1bii2.1
    con1bii
    bicomi
end
