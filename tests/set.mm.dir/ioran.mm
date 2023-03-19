include "wn.mm"
include "wi.mm"
include "wa.mm"
include "wo.mm"
include "pm4.65.mm"
include "pm4.64.mm"
include "xchnxbi.mm"

theorem ioran
  param wph: wff ph
  param wps: wff ps


  assert |- ( -. ( ph \/ ps ) <-> ( -. ph /\ -. ps ) )

  proof
    wph
    wn
    #
    wps
    wi
    @0
    wps
    wn
    wa
    wph
    wps
    wo
    wph
    wps
    pm4.65
    wph
    wps
    pm4.64
    xchnxbi
end
