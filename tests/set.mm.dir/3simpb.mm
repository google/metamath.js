include "w3a.mm"
include "wa.mm"
include "3ancomb.mm"
include "3simpa.mm"
include "sylbi.mm"

theorem 3simpb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) -> ( ph /\ ch ) )

  proof
    wph
    wps
    wch
    w3a
    wph
    wch
    wps
    w3a
    wph
    wch
    wa
    wph
    wps
    wch
    3ancomb
    wph
    wch
    wps
    3simpa
    sylbi
end
