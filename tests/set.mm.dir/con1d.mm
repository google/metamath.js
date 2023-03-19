include "wn.mm"
include "notnot.mm"
include "syl6.mm"
include "con4d.mm"

theorem con1d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume con1d.1: |- ( ph -> ( -. ps -> ch ) )


  assert |- ( ph -> ( -. ch -> ps ) )

  proof
    wph
    wps
    wch
    wn
    #
    wph
    wps
    wn
    wch
    @0
    wn
    con1d.1
    wch
    notnot
    syl6
    con4d
end
