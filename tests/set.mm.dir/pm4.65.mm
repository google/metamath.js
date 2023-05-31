include "wn.mm"
include "pm4.61.mm"

theorem pm4.65
  param wph: wff ph
  param wps: wff ps


  assert |- ( -. ( -. ph -> ps ) <-> ( -. ph /\ -. ps ) )

  proof
    wph
    wn
    wps
    pm4.61
end
