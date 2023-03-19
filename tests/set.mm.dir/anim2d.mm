include "idd.mm"
include "anim12d.mm"

theorem anim2d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
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
