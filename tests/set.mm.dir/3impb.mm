include "exp32.mm"
include "3imp.mm"

theorem 3impb
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume 3impb.1: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    3impb.1
    exp32
    3imp
end
