include "wo.mm"
include "w3o.mm"
include "wn.mm"
include "wb.mm"
include "biorf.mm"
include "syl.mm"
include "3bior1fd.mm"
include "bitrd.mm"

theorem 3bior2fd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3biorfd.1: |- ( ph -> -. th )
  assume 3biorfd.2: |- ( ph -> -. ch )


  assert |- ( ph -> ( ps <-> ( th \/ ch \/ ps ) ) )

  proof
    wph
    wps
    wch
    wps
    wo
    #
    wth
    wch
    wps
    w3o
    wph
    wch
    wn
    wps
    @0
    wb
    3biorfd.2
    wch
    wps
    biorf
    syl
    wph
    wps
    wch
    wth
    3biorfd.1
    3bior1fd
    bitrd
end
