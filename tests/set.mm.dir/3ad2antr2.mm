include "adantrl.mm"
include "3adantr3.mm"

theorem 3ad2antr2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3ad2antl.1: |- ( ( ph /\ ch ) -> th )


  assert |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th )

  proof
    wph
    wps
    wch
    wth
    wta
    wph
    wch
    wth
    wps
    3ad2antl.1
    adantrl
    3adantr3
end
