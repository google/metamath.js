include "wn.mm"
include "bicomd.mm"
include "con2bid.mm"

theorem con1bid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume con1bid.1: |- ( ph -> ( -. ps <-> ch ) )


  assert |- ( ph -> ( -. ch <-> ps ) )

  proof
    wph
    wps
    wch
    wn
    wph
    wch
    wps
    wph
    wps
    wn
    wch
    con1bid.1
    bicomd
    con2bid
    bicomd
end
