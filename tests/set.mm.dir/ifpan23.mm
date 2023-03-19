include "wif.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "ifpan123g.mm"
include "an4.mm"
include "dfifp4.mm"
include "ordi.mm"
include "anbi12i.mm"
include "bitr2i.mm"
include "3bitri.mm"

theorem ifpan23
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( if- ( ph , ps , ch ) /\ if- ( ph , th , ta ) ) <-> if- ( ph , ( ps /\ th ) , ( ch /\ ta ) ) )

  proof
    wph
    wps
    wch
    wif
    wph
    wth
    wta
    wif
    wa
    wph
    wn
    #
    wps
    wo
    #
    wph
    wch
    wo
    #
    wa
    @0
    wth
    wo
    #
    wph
    wta
    wo
    #
    wa
    wa
    @1
    @3
    wa
    #
    @2
    @4
    wa
    #
    wa
    #
    wph
    wps
    wth
    wa
    #
    wch
    wta
    wa
    #
    wif
    #
    wph
    wph
    wps
    wth
    wch
    wta
    ifpan123g
    @1
    @2
    @3
    @4
    an4
    @10
    @0
    @8
    wo
    #
    wph
    @9
    wo
    #
    wa
    @7
    wph
    @8
    @9
    dfifp4
    @11
    @5
    @12
    @6
    @0
    wps
    wth
    ordi
    wph
    wch
    wta
    ordi
    anbi12i
    bitr2i
    3bitri
end
