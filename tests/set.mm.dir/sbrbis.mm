include "wb.mm"
include "wsb.mm"
include "sbbi.mm"
include "bibi1i.mm"
include "bitri.mm"

theorem sbrbis
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume sbrbis.1: |- ( [ y / x ] ph <-> ps )


  assert |- ( [ y / x ] ( ph <-> ch ) <-> ( ps <-> [ y / x ] ch ) )

  proof
    wph
    wch
    wb
    vx
    vy
    wsb
    wph
    vx
    vy
    wsb
    #
    wch
    vx
    vy
    wsb
    #
    wb
    wps
    @1
    wb
    wph
    wch
    vx
    vy
    sbbi
    @0
    wps
    @1
    sbrbis.1
    bibi1i
    bitri
end
