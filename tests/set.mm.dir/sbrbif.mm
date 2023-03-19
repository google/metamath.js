include "wb.mm"
include "wsb.mm"
include "sbrbis.mm"
include "sbf.mm"
include "bibi2i.mm"
include "bitri.mm"

theorem sbrbif
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume sbrbif.1: |- F/ x ch
  assume sbrbif.2: |- ( [ y / x ] ph <-> ps )


  assert |- ( [ y / x ] ( ph <-> ch ) <-> ( ps <-> ch ) )

  proof
    wph
    wch
    wb
    vx
    vy
    wsb
    wps
    wch
    vx
    vy
    wsb
    #
    wb
    wps
    wch
    wb
    wph
    wps
    wch
    vx
    vy
    sbrbif.2
    sbrbis
    @0
    wch
    wps
    wch
    vx
    vy
    sbrbif.1
    sbf
    bibi2i
    bitri
end
