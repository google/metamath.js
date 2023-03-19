include "wa.mm"
include "wi.mm"
include "imp.mm"

theorem imp31
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume impd.1: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- ( ( ( ph /\ ps ) /\ ch ) -> th )

  proof
    wph
    wps
    wa
    wch
    wth
    wph
    wps
    wch
    wth
    wi
    impd.1
    imp
    imp
end
