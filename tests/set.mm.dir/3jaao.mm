include "w3a.mm"
include "wi.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "3jaod.mm"

theorem 3jaao
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume 3jaao.1: |- ( ph -> ( ps -> ch ) )
  assume 3jaao.2: |- ( th -> ( ta -> ch ) )
  assume 3jaao.3: |- ( et -> ( ze -> ch ) )


  assert |- ( ( ph /\ th /\ et ) -> ( ( ps \/ ta \/ ze ) -> ch ) )

  proof
    wph
    wth
    wet
    w3a
    wps
    wch
    wta
    wze
    wph
    wth
    wps
    wch
    wi
    wet
    3jaao.1
    3ad2ant1
    wth
    wph
    wta
    wch
    wi
    wet
    3jaao.2
    3ad2ant2
    wet
    wph
    wze
    wch
    wi
    wth
    3jaao.3
    3ad2ant3
    3jaod
end
