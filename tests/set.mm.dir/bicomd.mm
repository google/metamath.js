include "wb.mm"
include "bicom.mm"
include "sylib.mm"

theorem bicomd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume bicomd.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( ch <-> ps ) )

  proof
    wph
    wps
    wch
    wb
    wch
    wps
    wb
    bicomd.1
    wps
    wch
    bicom
    sylib
end
