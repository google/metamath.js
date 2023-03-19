include "wn.mm"
include "imor.mm"

theorem pm4.62
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> -. ps ) <-> ( -. ph \/ -. ps ) )

  proof
    wph
    wps
    wn
    imor
end
