include "cab.mm"
include "wcel.mm"
include "wsbc.mm"
include "cbvab.mm"
include "eleq2i.mm"
include "df-sbc.mm"
include "3bitr4i.mm"

theorem cbvsbc
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume cbvsbc.1: |- F/ y ph
  assume cbvsbc.2: |- F/ x ps
  assume cbvsbc.3: |- ( x = y -> ( ph <-> ps ) )


  assert |- ( [. A / x ]. ph <-> [. A / y ]. ps )

  proof
    cA
    wph
    vx
    cab
    #
    wcel
    cA
    wps
    vy
    cab
    #
    wcel
    wph
    vx
    cA
    wsbc
    wps
    vy
    cA
    wsbc
    @0
    @1
    cA
    wph
    wps
    vx
    vy
    cbvsbc.1
    cbvsbc.2
    cbvsbc.3
    cbvab
    eleq2i
    wph
    vx
    cA
    df-sbc
    wps
    vy
    cA
    df-sbc
    3bitr4i
end
