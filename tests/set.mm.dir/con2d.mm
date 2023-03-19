include "wn.mm"
include "notnotr.mm"
include "syl5.mm"
include "con4d.mm"

theorem con2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
