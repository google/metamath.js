include "wb.mm"
include "wsb.mm"
include "sbbi.mm"
include "bibi2i.mm"
include "bitri.mm"

theorem sblbis
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume sblbis.1: |- ( [ y / x ] ph <-> ps )


  assert |- ( [ y / x ] ( ch <-> ph ) <-> ( [ y / x ] ch <-> ps ) )

  proof
    wch
    wph
    wb
    vx
    vy
    wsb
    wch
    vx
    vy
    wsb
    #
    wph
    vx
    vy
    wsb
    #
    wb
    @0
    wps
    wb
    wch
    wph
    vx
    vy
    sbbi
    @1
    wps
    @0
    sblbis.1
    bibi2i
    bitri
end
