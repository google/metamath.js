include "id.mm"
include "ad2antrr.mm"

theorem simpll
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph /\ ps ) /\ ch ) -> ph )

  proof
    wph
    wph
    wps
    wch
    wph
    id
    ad2antrr
end
