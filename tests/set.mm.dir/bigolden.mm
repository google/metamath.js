include "wi.mm"
include "wa.mm"
include "wb.mm"
include "wo.mm"
include "pm4.71.mm"
include "pm4.72.mm"
include "bicom.mm"
include "3bitr3ri.mm"

theorem bigolden
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph /\ ps ) <-> ph ) <-> ( ps <-> ( ph \/ ps ) ) )

  proof
    wph
    wps
    wi
    wph
    wph
    wps
    wa
    #
    wb
    wps
    wph
    wps
    wo
    wb
    @0
    wph
    wb
    wph
    wps
    pm4.71
    wph
    wps
    pm4.72
    wph
    @0
    bicom
    3bitr3ri
end
