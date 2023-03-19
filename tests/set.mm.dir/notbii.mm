include "wb.mm"
include "wn.mm"
include "notbi.mm"
include "mpbi.mm"

theorem notbii
  let wph: wff ph
  let wps: wff ps
  assume notbii.1: |- ( ph <-> ps )


  assert |- ( -. ph <-> -. ps )

  proof
    wph
    wps
    wb
    wph
    wn
    wps
    wn
    wb
    notbii.1
    wph
    wps
    notbi
    mpbi
end
