include "wi.mm"
include "a1i.mm"
include "mpd.mm"

theorem syl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
