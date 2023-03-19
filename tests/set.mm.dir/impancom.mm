include "wi.mm"
include "ex.mm"
include "com23.mm"
include "imp.mm"

theorem impancom
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume impancom.1: |- ( ( ph /\ ps ) -> ( ch -> th ) )


  assert |- ( ( ph /\ ch ) -> ( ps -> th ) )

  proof
    wph
    wch
    wps
    wth
    wi
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    wi
    impancom.1
    ex
    com23
    imp
end
