include "wn.mm"
include "wb.mm"
include "con2bi.mm"
include "sylibr.mm"

theorem con2bid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume con2bid.1: |- ( ph -> ( ps <-> -. ch ) )


  assert |- ( ph -> ( ch <-> -. ps ) )

  proof
    wph
    wps
    wch
    wn
    wb
    wch
    wps
    wn
    wb
    con2bid.1
    wch
    wps
    con2bi
    sylibr
end
