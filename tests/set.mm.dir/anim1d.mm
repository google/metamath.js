include "idd.mm"
include "anim12d.mm"

theorem anim1d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume anim1d.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ( ps /\ th ) -> ( ch /\ th ) ) )

  proof
    wph
    wps
    wch
    wth
    wth
    anim1d.1
    wph
    wth
    idd
    anim12d
end
