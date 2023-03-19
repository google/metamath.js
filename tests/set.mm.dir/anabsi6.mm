include "ancomsd.mm"
include "anabsi5.mm"

theorem anabsi6
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume anabsi6.1: |- ( ph -> ( ( ps /\ ph ) -> ch ) )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wch
    wph
    wps
    wph
    wch
    anabsi6.1
    ancomsd
    anabsi5
end
