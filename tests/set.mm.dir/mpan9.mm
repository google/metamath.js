include "syl5.mm"
include "impcom.mm"

theorem mpan9
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume mpan9.1: |- ( ph -> ps )
  assume mpan9.2: |- ( ch -> ( ps -> th ) )


  assert |- ( ( ph /\ ch ) -> th )

  proof
    wch
    wph
    wth
    wph
    wps
    wch
    wth
    mpan9.1
    mpan9.2
    syl5
    impcom
end
