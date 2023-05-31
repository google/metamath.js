include "wa.mm"
include "pm5.32d.mm"
include "ancom.mm"
include "3bitr4g.mm"

theorem pm5.32rd
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume pm5.32d.1: |- ( ph -> ( ps -> ( ch <-> th ) ) )


  assert |- ( ph -> ( ( ch /\ ps ) <-> ( th /\ ps ) ) )

  proof
    wph
    wps
    wch
    wa
    wps
    wth
    wa
    wch
    wps
    wa
    wth
    wps
    wa
    wph
    wps
    wch
    wth
    pm5.32d.1
    pm5.32d
    wch
    wps
    ancom
    wth
    wps
    ancom
    3bitr4g
end
