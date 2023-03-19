include "wn.mm"
include "wb.mm"
include "nbn2.mm"
include "bicom.mm"
include "syl6rbb.mm"

theorem bibif
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ps -> ( ( ph <-> ps ) <-> -. ph ) )

  proof
    wps
    wn
    wph
    wn
    wps
    wph
    wb
    wph
    wps
    wb
    wps
    wph
    nbn2
    wps
    wph
    bicom
    syl6rbb
end
