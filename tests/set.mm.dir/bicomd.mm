include "wb.mm"
include "bicom.mm"
include "sylib.mm"

theorem bicomd
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
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
