include "a1i.mm"
include "mpdan.mm"

theorem mpan2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mpan2.1: |- ps
  assume mpan2.2: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    wps
    wph
    mpan2.1
    a1i
    mpan2.2
    mpdan
end
