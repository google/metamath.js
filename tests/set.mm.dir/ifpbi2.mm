include "wb.mm"
include "wi.mm"
include "wn.mm"
include "wa.mm"
include "wif.mm"
include "imbi2.mm"
include "anbi1d.mm"
include "dfifp2.mm"
include "3bitr4g.mm"

theorem ifpbi2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph <-> ps ) -> ( if- ( ch , ph , th ) <-> if- ( ch , ps , th ) ) )

  proof
    wph
    wps
    wb
    #
    wch
    wph
    wi
    #
    wch
    wn
    wth
    wi
    #
    wa
    wch
    wps
    wi
    #
    @2
    wa
    wch
    wph
    wth
    wif
    wch
    wps
    wth
    wif
    @0
    @1
    @3
    @2
    wph
    wps
    wch
    imbi2
    anbi1d
    wch
    wph
    wth
    dfifp2
    wch
    wps
    wth
    dfifp2
    3bitr4g
end
