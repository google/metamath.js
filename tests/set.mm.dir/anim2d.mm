include "idd.mm"
include "anim12d.mm"

theorem anim2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume anim1d.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ( th /\ ps ) -> ( th /\ ch ) ) )

  proof
    wph
    wth
    wth
    wps
    wch
    wph
    wth
    idd
    anim1d.1
    anim12d
end
