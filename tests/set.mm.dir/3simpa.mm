include "w3a.mm"
include "wa.mm"
include "df-3an.mm"
include "simplbi.mm"

theorem 3simpa
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) -> ( ph /\ ps ) )

  proof
    wph
    wps
    wch
    w3a
    wph
    wps
    wa
    wch
    wph
    wps
    wch
    df-3an
    simplbi
end
