include "biimpri.mm"
include "sylan2.mm"

theorem sylan2br
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume sylan2br.1: |- ( ch <-> ph )
  assume sylan2br.2: |- ( ( ps /\ ch ) -> th )


  assert |- ( ( ps /\ ph ) -> th )

  proof
    wph
    wps
    wch
    wth
    wch
    wph
    sylan2br.1
    biimpri
    sylan2br.2
    sylan2
end
