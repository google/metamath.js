include "a1i.mm"
include "mpbird.mm"

theorem mpbiri
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mpbiri.min: |- ch
  assume mpbiri.maj: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wch
    wch
    wph
    mpbiri.min
    a1i
    mpbiri.maj
    mpbird
end
