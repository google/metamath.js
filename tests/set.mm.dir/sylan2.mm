include "adantl.mm"
include "syldan.mm"

theorem sylan2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
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
