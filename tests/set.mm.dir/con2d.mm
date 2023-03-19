include "wn.mm"
include "notnotr.mm"
include "syl5.mm"
include "con4d.mm"

theorem con2d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume con2d.1: |- ( ph -> ( ps -> -. ch ) )


  assert |- ( ph -> ( ch -> -. ps ) )

  proof
    wph
    wps
    wn
    #
    wch
    @0
    wn
    wps
    wph
    wch
    wn
    wps
    notnotr
    con2d.1
    syl5
    con4d
end
