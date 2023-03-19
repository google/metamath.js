include "mpanr1.mm"
include "mpan2.mm"

theorem mpanr12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpanr12.1: |- ps
  assume mpanr12.2: |- ch
  assume mpanr12.3: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ph -> th )

  proof
    wph
    wch
    wth
    mpanr12.2
    wph
    wps
    wch
    wth
    mpanr12.1
    mpanr12.3
    mpanr1
    mpan2
end
