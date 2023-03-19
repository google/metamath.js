include "anandis.mm"
include "3impb.mm"

theorem 3impdi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3impdi.1: |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) ) -> th )


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
    3impdi.1
    anandis
    3impb
end
