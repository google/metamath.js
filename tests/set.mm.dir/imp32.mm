include "wa.mm"
include "impd.mm"
include "imp.mm"

theorem imp32
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume impd.1: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- ( ( ph /\ ( ps /\ ch ) ) -> th )

  proof
    wph
    wps
    wch
    wa
    wth
    wph
    wps
    wch
    wth
    impd.1
    impd
    imp
end
