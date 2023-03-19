include "wa.mm"
include "wn.mm"
include "wi.mm"
include "wo.mm"
include "imnan.mm"
include "pm4.62.mm"
include "bitr3i.mm"

theorem ianor
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph /\ ps ) <-> ( -. ph \/ -. ps ) )

  proof
    wph
    wps
    wa
    wn
    wph
    wps
    wn
    #
    wi
    wph
    wn
    @0
    wo
    wph
    wps
    imnan
    wph
    wps
    pm4.62
    bitr3i
end
