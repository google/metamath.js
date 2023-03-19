include "adantl.mm"
include "3adant1.mm"

theorem 3ad2ant3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3ad2ant.1: |- ( ph -> ch )


  assert |- ( ( ps /\ th /\ ph ) -> ch )

  proof
    wth
    wph
    wch
    wps
    wph
    wch
    wth
    3ad2ant.1
    adantl
    3adant1
end
