include "adantrl.mm"
include "3adantr1.mm"

theorem 3ad2antr3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3ad2antl.1: |- ( ( ph /\ ch ) -> th )


  assert |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th )

  proof
    wph
    wta
    wch
    wth
    wps
    wph
    wch
    wth
    wta
    3ad2antl.1
    adantrl
    3adantr1
end
