include "wa.mm"
include "simpl.mm"
include "ad2antrr.mm"

theorem simplll
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ph )

  proof
    wph
    wps
    wa
    wph
    wch
    wth
    wph
    wps
    simpl
    ad2antrr
end
