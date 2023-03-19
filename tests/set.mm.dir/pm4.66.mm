include "wn.mm"
include "pm4.64.mm"

theorem pm4.66
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph -> -. ps ) <-> ( ph \/ -. ps ) )

  proof
    wph
    wps
    wn
    pm4.64
end
