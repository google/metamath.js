include "wb.mm"
include "wa.mm"
include "wi.mm"
include "wn.mm"
include "wif.mm"
include "simpl.mm"
include "imbi1d.mm"
include "notbi.mm"
include "imbi12.mm"
include "sylbi.mm"
include "imp.mm"
include "anbi12d.mm"
include "dfifp2.mm"
include "3bitr4g.mm"

theorem ifpbi13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ph <-> ps ) /\ ( ch <-> th ) ) -> ( if- ( ph , ta , ch ) <-> if- ( ps , ta , th ) ) )

  proof
    wph
    wps
    wb
    #
    wch
    wth
    wb
    #
    wa
    #
    wph
    wta
    wi
    #
    wph
    wn
    #
    wch
    wi
    #
    wa
    wps
    wta
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
    wta
    wch
    wif
    wps
    wta
    wth
    wif
    @2
    @3
    @6
    @5
    @8
    @2
    wph
    wps
    wta
    @0
    @1
    simpl
    imbi1d
    @0
    @1
    @5
    @8
    wb
    #
    @0
    @4
    @7
    wb
    @1
    @9
    wi
    wph
    wps
    notbi
    @4
    @7
    wch
    wth
    imbi12
    sylbi
    imp
    anbi12d
    wph
    wta
    wch
    dfifp2
    wps
    wta
    wth
    dfifp2
    3bitr4g
end
