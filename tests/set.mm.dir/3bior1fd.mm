include "wo.mm"
include "w3o.mm"
include "wn.mm"
include "wb.mm"
include "biorf.mm"
include "syl.mm"
include "3orass.mm"
include "syl6bbr.mm"

theorem 3bior1fd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3biorfd.1: |- ( ph -> -. th )


  assert |- ( ph -> ( ( ch \/ ps ) <-> ( th \/ ch \/ ps ) ) )

  proof
    wph
    wch
    wps
    wo
    #
    wth
    @0
    wo
    #
    wth
    wch
    wps
    w3o
    wph
    wth
    wn
    @0
    @1
    wb
    3biorfd.1
    wth
    @0
    biorf
    syl
    wth
    wch
    wps
    3orass
    syl6bbr
end
