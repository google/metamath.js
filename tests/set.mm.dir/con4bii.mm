include "wb.mm"
include "wn.mm"
include "notbi.mm"
include "mpbir.mm"

theorem con4bii
  let wph: wff ph
  let wps: wff ps
  assume con4bii.1: |- ( -. ph <-> -. ps )


  assert |- ( ph <-> ps )

  proof
    wph
    wps
    wb
    wph
    wn
    wps
    wn
    wb
    con4bii.1
    wph
    wps
    notbi
    mpbir
end
