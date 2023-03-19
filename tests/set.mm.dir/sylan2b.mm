include "biimpi.mm"
include "sylan2.mm"

theorem sylan2b
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume sylan2b.1: |- ( ph <-> ch )
  assume sylan2b.2: |- ( ( ps /\ ch ) -> th )


  assert |- ( ( ps /\ ph ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wch
    sylan2b.1
    biimpi
    sylan2b.2
    sylan2
end
