include "cab.mm"
include "wcel.mm"
include "wsbc.mm"
include "abbid.mm"
include "eleq2d.mm"
include "df-sbc.mm"
include "3bitr4g.mm"

theorem sbcbid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume sbcbid.1: |- F/ x ph
  assume sbcbid.2: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( [. A / x ]. ps <-> [. A / x ]. ch ) )

  proof
    wph
    cA
    wps
    vx
    cab
    #
    wcel
    cA
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
    cA
    wsbc
    wph
    @0
    @1
    cA
    wph
    wps
    wch
    vx
    sbcbid.1
    sbcbid.2
    abbid
    eleq2d
    wps
    vx
    cA
    df-sbc
    wch
    vx
    cA
    df-sbc
    3bitr4g
end
