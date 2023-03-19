include "wi.mm"
include "ex.mm"
include "impd.mm"

theorem expimpd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume expimpd.1: |- ( ( ph /\ ps ) -> ( ch -> th ) )


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
    wi
    expimpd.1
    ex
    impd
end
