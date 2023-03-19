include "wa.mm"
include "adantr.mm"
include "mpdan.mm"

theorem mpidan
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpidan.1: |- ( ph -> ch )
  assume mpidan.2: |- ( ( ( ph /\ ps ) /\ ch ) -> th )


  assert |- ( ( ph /\ ps ) -> th )

  proof
    wph
    wps
    wa
    wch
    wth
    wph
    wch
    wps
    mpidan.1
    adantr
    mpidan.2
    mpdan
end
