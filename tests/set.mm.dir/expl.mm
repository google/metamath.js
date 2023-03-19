include "exp31.mm"
include "impd.mm"

theorem expl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume expl.1: |- ( ( ( ph /\ ps ) /\ ch ) -> th )


  assert |- ( ph -> ( ( ps /\ ch ) -> th ) )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    expl.1
    exp31
    impd
end
