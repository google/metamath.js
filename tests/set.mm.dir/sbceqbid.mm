include "cab.mm"
include "wcel.mm"
include "wsbc.mm"
include "abbidv.mm"
include "eleq12d.mm"
include "df-sbc.mm"
include "3bitr4g.mm"

theorem sbceqbid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume sbceqbid.1: |- ( ph -> A = B )
  assume sbceqbid.2: |- ( ph -> ( ps <-> ch ) )

  disjoint ph x
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
    sbceqbid.1
    wph
    wps
    wch
    vx
    sbceqbid.2
    abbidv
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
