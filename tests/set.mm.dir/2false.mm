include "wn.mm"
include "2th.mm"
include "con4bii.mm"

theorem 2false
  let wph: wff ph
  let wps: wff ps
  assume 2false.1: |- -. ph
  assume 2false.2: |- -. ps


  assert |- ( ph <-> ps )

  proof
    wph
    wps
    wph
    wn
    wps
    wn
    2false.1
    2false.2
    2th
    con4bii
end
