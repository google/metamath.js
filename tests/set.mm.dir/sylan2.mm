include "adantl.mm"
include "syldan.mm"

theorem sylan2
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume sylan2.1: |- ( ph -> ch )
  assume sylan2.2: |- ( ( ps /\ ch ) -> th )


  assert |- ( ( ps /\ ph ) -> th )

  proof
    wps
    wph
    wch
    wth
    wph
    wch
    wps
    sylan2.1
    adantl
    sylan2.2
    syldan
end
