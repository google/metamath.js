include "wal.mm"
include "dfvd2i.mm"
include "alrimdv.mm"
include "dfvd2ir.mm"

theorem gen21
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume gen21.1: |- (. ph ,. ps ->. ch ).

  disjoint ph x
  disjoint ps x
  assert |- (. ph ,. ps ->. A. x ch ).

  proof
    wph
    wps
    wch
    vx
    wal
    wph
    wps
    wch
    vx
    wph
    wps
    wch
    gen21.1
    dfvd2i
    alrimdv
    dfvd2ir
end
