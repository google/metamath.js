include "wal.mm"
include "dfvd2i.mm"
include "alrimdh.mm"
include "dfvd2ir.mm"

theorem gen21nv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume gen21nv.1: |- ( ph -> A. x ph )
  assume gen21nv.2: |- ( ps -> A. x ps )
  assume gen21nv.3: |- (. ph ,. ps ->. ch ).


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
    gen21nv.1
    gen21nv.2
    wph
    wps
    wch
    gen21nv.3
    dfvd2i
    alrimdh
    dfvd2ir
end
