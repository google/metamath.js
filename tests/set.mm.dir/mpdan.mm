include "id.mm"
include "syl2anc.mm"

theorem mpdan
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mpdan.1: |- ( ph -> ps )
  assume mpdan.2: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ph -> ch )

  proof
    wph
    wph
    wps
    wch
    wph
    id
    mpdan.1
    mpdan.2
    syl2anc
end
