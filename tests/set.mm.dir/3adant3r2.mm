include "3expb.mm"
include "3adantr2.mm"

theorem 3adant3r2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3exp.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th )

  proof
    wph
    wps
    wch
    wth
    wta
    wph
    wps
    wch
    wth
    3exp.1
    3expb
    3adantr2
end
