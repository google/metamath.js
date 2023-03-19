include "bicomi.mm"
include "mtbi.mm"

theorem mtbir
  let wph: wff ph
  let wps: wff ps
  assume mtbir.1: |- -. ps
  assume mtbir.2: |- ( ph <-> ps )


  assert |- -. ph

  proof
    wps
    wph
    mtbir.1
    wph
    wps
    mtbir.2
    bicomi
    mtbi
end
