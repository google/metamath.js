include "wb.mm"
include "a1i.mm"
include "bitrd.mm"

theorem syl5bb
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume syl5bb.1: |- ( ph <-> ps )
  assume syl5bb.2: |- ( ch -> ( ps <-> th ) )


  assert |- ( ch -> ( ph <-> th ) )

  proof
    wch
    wph
    wps
    wth
    wph
    wps
    wb
    wch
    syl5bb.1
    a1i
    syl5bb.2
    bitrd
end
