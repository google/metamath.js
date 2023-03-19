include "wn.mm"
include "notbii.mm"
include "bitr3i.mm"

theorem xchnxbi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume xchnxbi.1: |- ( -. ph <-> ps )
  assume xchnxbi.2: |- ( ph <-> ch )


  assert |- ( -. ch <-> ps )

  proof
    wch
    wn
    wph
    wn
    wps
    wph
    wch
    xchnxbi.2
    notbii
    xchnxbi.1
    bitr3i
end
