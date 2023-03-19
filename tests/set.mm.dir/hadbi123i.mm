include "whad.mm"
include "wb.mm"
include "wtru.mm"
include "a1i.mm"
include "hadbi123d.mm"
include "trud.mm"

theorem hadbi123i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume hadbii.1: |- ( ph <-> ps )
  assume hadbii.2: |- ( ch <-> th )
  assume hadbii.3: |- ( ta <-> et )


  assert |- ( hadd ( ph , ch , ta ) <-> hadd ( ps , th , et ) )

  proof
    wph
    wch
    wta
    whad
    wps
    wth
    wet
    whad
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
    hadbii.1
    a1i
    wch
    wth
    wb
    wtru
    hadbii.2
    a1i
    wta
    wet
    wb
    wtru
    hadbii.3
    a1i
    hadbi123d
    trud
end
