include "biimpd.mm"
include "sylcom.mm"

theorem mpbidi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpbidi.min: |- ( th -> ( ph -> ps ) )
  assume mpbidi.maj: |- ( ph -> ( ps <-> ch ) )


  assert |- ( th -> ( ph -> ch ) )

  proof
    wth
    wph
    wps
    wch
    mpbidi.min
    wph
    wps
    wch
    mpbidi.maj
    biimpd
    sylcom
end
