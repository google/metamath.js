include "wb.mm"
include "a1i.mm"
include "bitrd.mm"

theorem syl6bb
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume syl6bb.1: |- ( ph -> ( ps <-> ch ) )
  assume syl6bb.2: |- ( ch <-> th )


  assert |- ( ph -> ( ps <-> th ) )

  proof
    wph
    wps
    wch
    wth
    syl6bb.1
    wch
    wth
    wb
    wph
    syl6bb.2
    a1i
    bitrd
end
