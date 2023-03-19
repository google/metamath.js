include "wmo.mm"
include "wb.mm"
include "wtru.mm"
include "a1i.mm"
include "mobidv.mm"
include "trud.mm"

theorem mobii
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume mobii.1: |- ( ps <-> ch )


  assert |- ( E* x ps <-> E* x ch )

  proof
    wps
    vx
    wmo
    wch
    vx
    wmo
    wb
    wtru
    wps
    wch
    vx
    wps
    wch
    wb
    wtru
    mobii.1
    a1i
    mobidv
    trud
end
