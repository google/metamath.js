include "wb.mm"
include "wi.mm"
include "wn.mm"
include "wa.mm"
include "wif.mm"
include "imbi1.mm"
include "notbi.mm"
include "biimpi.mm"
include "imbi1d.mm"
include "anbi12d.mm"
include "dfifp2.mm"
include "3bitr4g.mm"

theorem ifpbi1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph <-> ps ) -> ( if- ( ph , ch , th ) <-> if- ( ps , ch , th ) ) )

  proof
    wph
    wps
    wb
    #
    wph
    wch
    wi
    #
    wph
    wn
    #
    wth
    wi
    #
    wa
    wps
    wch
    wi
    #
    wps
    wn
    #
    wth
    wi
    #
    wa
    wph
    wch
    wth
    wif
    wps
    wch
    wth
    wif
    @0
    @1
    @4
    @3
    @6
    wph
    wps
    wch
    imbi1
    @0
    @2
    @5
    wth
    @0
    @2
    @5
    wb
    wph
    wps
    notbi
    biimpi
    imbi1d
    anbi12d
    wph
    wch
    wth
    dfifp2
    wps
    wch
    wth
    dfifp2
    3bitr4g
end
