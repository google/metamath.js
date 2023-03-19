include "wb.mm"
include "wi.mm"
include "wn.mm"
include "wa.mm"
include "wif.mm"
include "imbi2.mm"
include "anbi2d.mm"
include "dfifp2.mm"
include "3bitr4g.mm"

theorem ifpbi3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph <-> ps ) -> ( if- ( ch , th , ph ) <-> if- ( ch , th , ps ) ) )

  proof
    wph
    wps
    wb
    #
    wch
    wth
    wi
    #
    wch
    wn
    #
    wph
    wi
    #
    wa
    @1
    @2
    wps
    wi
    #
    wa
    wch
    wth
    wph
    wif
    wch
    wth
    wps
    wif
    @0
    @3
    @4
    @1
    wph
    wps
    @2
    imbi2
    anbi2d
    wch
    wth
    wph
    dfifp2
    wch
    wth
    wps
    dfifp2
    3bitr4g
end
