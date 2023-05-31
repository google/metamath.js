include "syl2im.mm"
include "pm2.43i.mm"

theorem sylc
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume sylc.1: |- ( ph -> ps )
  assume sylc.2: |- ( ph -> ch )
  assume sylc.3: |- ( ps -> ( ch -> th ) )


  assert |- ( ph -> th )

  proof
    wph
    wth
    wph
    wps
    wph
    wch
    wth
    sylc.1
    sylc.2
    sylc.3
    syl2im
    pm2.43i
end
