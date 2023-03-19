include "wa.mm"
include "biantrurd.mm"
include "bitr4d.mm"

theorem mpbirand
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpbirand.1: |- ( ph -> ch )
  assume mpbirand.2: |- ( ph -> ( ps <-> ( ch /\ th ) ) )


  assert |- ( ph -> ( ps <-> th ) )

  proof
    wph
    wps
    wch
    wth
    wa
    wth
    mpbirand.2
    wph
    wch
    wth
    mpbirand.1
    biantrurd
    bitr4d
end
