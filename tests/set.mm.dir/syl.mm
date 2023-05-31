include "wi.mm"
include "a1i.mm"
include "mpd.mm"

theorem syl
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume syl.1: |- ( ph -> ps )
  assume syl.2: |- ( ps -> ch )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    syl.1
    wps
    wch
    wi
    wph
    syl.2
    a1i
    mpd
end
