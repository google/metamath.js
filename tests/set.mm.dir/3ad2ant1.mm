include "adantr.mm"
include "3adant2.mm"

theorem 3ad2ant1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3ad2ant.1: |- ( ph -> ch )


  assert |- ( ( ph /\ ps /\ th ) -> ch )

  proof
    wph
    wth
    wch
    wps
    wph
    wch
    wth
    3ad2ant.1
    adantr
    3adant2
end
