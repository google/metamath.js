include "wi.mm"
include "wa.mm"
include "wb.mm"
include "pm4.71.mm"
include "ancom.mm"
include "bibi2i.mm"
include "bitri.mm"

theorem pm4.71r
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) <-> ( ph <-> ( ps /\ ph ) ) )

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
    wph
    wps
    wph
    wa
    #
    wb
    wph
    wps
    pm4.71
    @0
    @1
    wph
    wph
    wps
    ancom
    bibi2i
    bitri
end
