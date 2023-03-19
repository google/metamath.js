include "wal.mm"
include "dfvd3i.mm"
include "ggen31.mm"
include "dfvd3ir.mm"

theorem gen31
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  assume gen31.1: |- (. ph ,. ps ,. ch ->. th ).

  disjoint ch x
  disjoint ph x
  disjoint ps x
  assert |- (. ph ,. ps ,. ch ->. A. x th ).

  proof
    wph
    wps
    wch
    wth
    vx
    wal
    wph
    wps
    wch
    wth
    vx
    wph
    wps
    wch
    wth
    gen31.1
    dfvd3i
    ggen31
    dfvd3ir
end
