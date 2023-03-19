include "wb.mm"
include "wa.mm"
include "wi.mm"
include "wn.mm"
include "wif.mm"
include "simpl.mm"
include "imbi2d.mm"
include "simpr.mm"
include "anbi12d.mm"
include "dfifp2.mm"
include "3bitr4g.mm"

theorem ifpbi23
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ph <-> ps ) /\ ( ch <-> th ) ) -> ( if- ( ta , ph , ch ) <-> if- ( ta , ps , th ) ) )

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
    wta
    wph
    wi
    #
    wta
    wn
    #
    wch
    wi
    #
    wa
    wta
    wps
    wi
    #
    @4
    wth
    wi
    #
    wa
    wta
    wph
    wch
    wif
    wta
    wps
    wth
    wif
    @2
    @3
    @6
    @5
    @7
    @2
    wph
    wps
    wta
    @0
    @1
    simpl
    imbi2d
    @2
    wch
    wth
    @4
    @0
    @1
    simpr
    imbi2d
    anbi12d
    wta
    wph
    wch
    dfifp2
    wta
    wps
    wth
    dfifp2
    3bitr4g
end
