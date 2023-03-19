include "wa.mm"
include "simpr.mm"
include "ad2antrr.mm"

theorem simpllr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ps )

  proof
    wph
    wps
    wa
    wps
    wch
    wth
    wph
    wps
    simpr
    ad2antrr
end
