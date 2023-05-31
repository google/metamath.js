include "a1i.mm"
include "mpancom.mm"

theorem mpan
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume mpan.1: |- ph
  assume mpan.2: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ps -> ch )

  proof
    wph
    wps
    wch
    wph
    wps
    mpan.1
    a1i
    mpan.2
    mpancom
end
