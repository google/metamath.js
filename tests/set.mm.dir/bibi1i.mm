include "wb.mm"
include "bicom.mm"
include "bibi2i.mm"
include "3bitri.mm"

theorem bibi1i
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume bibi2i.1: |- ( ph <-> ps )


  assert |- ( ( ph <-> ch ) <-> ( ps <-> ch ) )

  proof
    wph
    wch
    wb
    wch
    wph
    wb
    wch
    wps
    wb
    wps
    wch
    wb
    wph
    wch
    bicom
    wph
    wps
    wch
    bibi2i.1
    bibi2i
    wch
    wps
    bicom
    3bitri
end
