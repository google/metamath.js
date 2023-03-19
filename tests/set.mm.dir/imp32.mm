include "wa.mm"
include "impd.mm"
include "imp.mm"

theorem imp32
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
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
