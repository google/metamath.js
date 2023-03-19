include "wn.mm"
include "con2bii.mm"
include "bicomi.mm"

theorem con2bii2
  let wph: wff ph
  let wps: wff ps
  assume con2bii2.1: |- ( ph <-> -. ps )


  assert |- ( -. ph <-> ps )

  proof
    wps
    wph
    wn
    wph
    wps
    con2bii2.1
    con2bii
    bicomi
end
