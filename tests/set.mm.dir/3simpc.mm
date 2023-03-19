include "w3a.mm"
include "wa.mm"
include "3anrot.mm"
include "3simpa.mm"
include "sylbi.mm"

theorem 3simpc
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) -> ( ps /\ ch ) )

  proof
    wph
    wps
    wch
    w3a
    wps
    wch
    wph
    w3a
    wps
    wch
    wa
    wph
    wps
    wch
    3anrot
    wps
    wch
    wph
    3simpa
    sylbi
end
