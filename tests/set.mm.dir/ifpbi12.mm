include "wb.mm"
include "wa.mm"
include "wi.mm"
include "wn.mm"
include "wif.mm"
include "imbi12.mm"
include "imp.mm"
include "simpl.mm"
include "notbid.mm"
include "imbi1d.mm"
include "anbi12d.mm"
include "dfifp2.mm"
include "3bitr4g.mm"

theorem ifpbi12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ph <-> ps ) /\ ( ch <-> th ) ) -> ( if- ( ph , ch , ta ) <-> if- ( ps , th , ta ) ) )

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
    wch
    wi
    #
    wph
    wn
    #
    wta
    wi
    #
    wa
    wps
    wth
    wi
    #
    wps
    wn
    #
    wta
    wi
    #
    wa
    wph
    wch
    wta
    wif
    wps
    wth
    wta
    wif
    @2
    @3
    @6
    @5
    @8
    @0
    @1
    @3
    @6
    wb
    wph
    wps
    wch
    wth
    imbi12
    imp
    @2
    @4
    @7
    wta
    @2
    wph
    wps
    @0
    @1
    simpl
    notbid
    imbi1d
    anbi12d
    wph
    wch
    wta
    dfifp2
    wps
    wth
    wta
    dfifp2
    3bitr4g
end
