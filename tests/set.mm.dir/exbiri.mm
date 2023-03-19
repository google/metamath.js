include "wa.mm"
include "biimpar.mm"
include "exp31.mm"

theorem exbiri
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume exbiri.1: |- ( ( ph /\ ps ) -> ( ch <-> th ) )


  assert |- ( ph -> ( ps -> ( th -> ch ) ) )

  proof
    wph
    wps
    wth
    wch
    wph
    wps
    wa
    wch
    wth
    exbiri.1
    biimpar
    exp31
end
