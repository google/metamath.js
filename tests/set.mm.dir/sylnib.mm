include "wb.mm"
include "a1i.mm"
include "mtbid.mm"

theorem sylnib
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume sylnib.1: |- ( ph -> -. ps )
  assume sylnib.2: |- ( ps <-> ch )


  assert |- ( ph -> -. ch )

  proof
    wph
    wps
    wch
    sylnib.1
    wps
    wch
    wb
    wph
    sylnib.2
    a1i
    mtbid
end
