include "wcad.mm"
include "wb.mm"
include "wtru.mm"
include "a1i.mm"
include "cadbi123d.mm"
include "trud.mm"

theorem cadbi123i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume cadbii.1: |- ( ph <-> ps )
  assume cadbii.2: |- ( ch <-> th )
  assume cadbii.3: |- ( ta <-> et )


  assert |- ( cadd ( ph , ch , ta ) <-> cadd ( ps , th , et ) )

  proof
    wph
    wch
    wta
    wcad
    wps
    wth
    wet
    wcad
    wb
    wtru
    wph
    wps
    wch
    wth
    wta
    wet
    wph
    wps
    wb
    wtru
    cadbii.1
    a1i
    wch
    wth
    wb
    wtru
    cadbii.2
    a1i
    wta
    wet
    wb
    wtru
    cadbii.3
    a1i
    cadbi123d
    trud
end
