include "cab.mm"
include "wcel.mm"
include "wsbc.mm"
include "abbid.mm"
include "eleq12d.mm"
include "df-sbc.mm"
include "3bitr4g.mm"

theorem sbceqbidf
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume sbceqbidf.1: |- F/ x ph
  assume sbceqbidf.2: |- ( ph -> A = B )
  assume sbceqbidf.3: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( [. A / x ]. ps <-> [. B / x ]. ch ) )

  proof
    wph
    cA
    wps
    vx
    cab
    #
    wcel
    cB
    wch
    vx
    cab
    #
    wcel
    wps
    vx
    cA
    wsbc
    wch
    vx
    cB
    wsbc
    wph
    cA
    cB
    @0
    @1
    sbceqbidf.2
    wph
    wps
    wch
    vx
    sbceqbidf.1
    sbceqbidf.3
    abbid
    eleq12d
    wps
    vx
    cA
    df-sbc
    wch
    vx
    cB
    df-sbc
    3bitr4g
end
