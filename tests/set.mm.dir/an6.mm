include "wa.mm"
include "w3a.mm"
include "an4.mm"
include "anbi1i.mm"
include "bitri.mm"
include "df-3an.mm"
include "anbi12i.mm"
include "3bitr4i.mm"

theorem an6
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( ph /\ ps /\ ch ) /\ ( th /\ ta /\ et ) ) <-> ( ( ph /\ th ) /\ ( ps /\ ta ) /\ ( ch /\ et ) ) )

  proof
    wph
    wps
    wa
    #
    wch
    wa
    #
    wth
    wta
    wa
    #
    wet
    wa
    #
    wa
    #
    wph
    wth
    wa
    #
    wps
    wta
    wa
    #
    wa
    #
    wch
    wet
    wa
    #
    wa
    #
    wph
    wps
    wch
    w3a
    #
    wth
    wta
    wet
    w3a
    #
    wa
    @5
    @6
    @8
    w3a
    @4
    @0
    @2
    wa
    #
    @8
    wa
    @9
    @0
    wch
    @2
    wet
    an4
    @12
    @7
    @8
    wph
    wps
    wth
    wta
    an4
    anbi1i
    bitri
    @10
    @1
    @11
    @3
    wph
    wps
    wch
    df-3an
    wth
    wta
    wet
    df-3an
    anbi12i
    @5
    @6
    @8
    df-3an
    3bitr4i
end
