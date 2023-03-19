include "wo.mm"
include "wif.mm"
include "wi.mm"
include "wn.mm"
include "wa.mm"
include "dfifp2.mm"
include "df-or.mm"
include "imbi2i.mm"
include "anbi12i.mm"
include "ifpimimb.mm"
include "imor.mm"
include "ifpnot23d.mm"
include "orbi1i.mm"
include "bitri.mm"
include "3bitr3i.mm"
include "3bitri.mm"

theorem ifpororb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( if- ( ph , ( ps \/ ch ) , ( th \/ ta ) ) <-> ( if- ( ph , ps , th ) \/ if- ( ph , ch , ta ) ) )

  proof
    wph
    wps
    wch
    wo
    #
    wth
    wta
    wo
    #
    wif
    wph
    @0
    wi
    #
    wph
    wn
    #
    @1
    wi
    #
    wa
    wph
    wps
    wn
    #
    wch
    wi
    #
    wi
    #
    @3
    wth
    wn
    #
    wta
    wi
    #
    wi
    #
    wa
    #
    wph
    wps
    wth
    wif
    #
    wph
    wch
    wta
    wif
    #
    wo
    #
    wph
    @0
    @1
    dfifp2
    @2
    @7
    @4
    @10
    @0
    @6
    wph
    wps
    wch
    df-or
    imbi2i
    @1
    @9
    @3
    wth
    wta
    df-or
    imbi2i
    anbi12i
    wph
    @6
    @9
    wif
    wph
    @5
    @8
    wif
    #
    @13
    wi
    #
    @11
    @14
    wph
    @5
    wch
    @8
    wta
    ifpimimb
    wph
    @6
    @9
    dfifp2
    @16
    @15
    wn
    #
    @13
    wo
    @14
    @15
    @13
    imor
    @17
    @12
    @13
    wph
    wps
    wth
    ifpnot23d
    orbi1i
    bitri
    3bitr3i
    3bitri
end
