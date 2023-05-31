include "wb.mm"
include "wi.mm"
include "wa.mm"
include "pm5.32.mm"
include "sylib.mm"

theorem pm5.32d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume pm5.32d.1: |- ( ph -> ( ps -> ( ch <-> th ) ) )


  assert |- ( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) )

  proof
    wph
    wps
    wch
    wth
    wb
    wi
    wps
    wch
    wa
    wps
    wth
    wa
    wb
    pm5.32d.1
    wps
    wch
    wth
    pm5.32
    sylib
end
