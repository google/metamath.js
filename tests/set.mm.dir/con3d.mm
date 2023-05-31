include "wn.mm"
include "notnotr.mm"
include "syl5.mm"
include "con1d.mm"

theorem con3d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume con3d.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( -. ch -> -. ps ) )

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
    wps
    notnotr
    con3d.1
    syl5
    con1d
end
