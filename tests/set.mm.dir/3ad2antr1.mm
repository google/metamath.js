include "adantrr.mm"
include "3adantr3.mm"

theorem 3ad2antr1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3ad2antl.1: |- ( ( ph /\ ch ) -> th )


  assert |- ( ( ph /\ ( ch /\ ps /\ ta ) ) -> th )

  proof
    wph
    wch
    wps
    wth
    wta
    wph
    wch
    wth
    wps
    3ad2antl.1
    adantrr
    3adantr3
end
