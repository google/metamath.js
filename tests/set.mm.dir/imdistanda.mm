include "wi.mm"
include "ex.mm"
include "imdistand.mm"

theorem imdistanda
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume imdistanda.1: |- ( ( ph /\ ps ) -> ( ch -> th ) )


  assert |- ( ph -> ( ( ps /\ ch ) -> ( ps /\ th ) ) )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    wi
    imdistanda.1
    ex
    imdistand
end
