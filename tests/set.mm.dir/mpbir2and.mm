include "wa.mm"
include "jca.mm"
include "mpbird.mm"

theorem mpbir2and
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpbir2and.1: |- ( ph -> ch )
  assume mpbir2and.2: |- ( ph -> th )
  assume mpbir2and.3: |- ( ph -> ( ps <-> ( ch /\ th ) ) )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wch
    wth
    wa
    wph
    wch
    wth
    mpbir2and.1
    mpbir2and.2
    jca
    mpbir2and.3
    mpbird
end
