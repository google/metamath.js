include "wn.mm"
include "pm4.63.mm"

theorem pm4.67
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( -. ph -> -. ps ) <-> ( -. ph /\ ps ) )

  proof
    wph
    wn
    wps
    pm4.63
end
