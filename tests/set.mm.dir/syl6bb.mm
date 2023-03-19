include "wb.mm"
include "a1i.mm"
include "bitrd.mm"

theorem syl6bb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
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
