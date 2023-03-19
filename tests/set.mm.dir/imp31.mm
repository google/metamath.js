include "wa.mm"
include "wi.mm"
include "imp.mm"

theorem imp31
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
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
