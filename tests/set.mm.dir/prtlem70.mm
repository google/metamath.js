include "wa.mm"
include "anass.mm"
include "anbi1i.mm"
include "anandi.mm"
include "ancom.mm"
include "3bitr4ri.mm"
include "bitri.mm"
include "3bitri.mm"
include "an4.mm"
include "anbi2i.mm"

theorem prtlem70
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( ( ps /\ et ) /\ ( ( ph /\ th ) /\ ( ch /\ ta ) ) ) /\ ph ) <-> ( ( ph /\ ( ps /\ ( ch /\ ( th /\ ta ) ) ) ) /\ et ) )

  proof
    wps
    wet
    wa
    #
    wph
    wth
    wa
    #
    wch
    wta
    wa
    #
    wa
    #
    wa
    #
    wph
    wa
    #
    wph
    wps
    wth
    wa
    #
    wa
    #
    @2
    wa
    #
    wet
    wa
    #
    wph
    @6
    @2
    wa
    #
    wa
    #
    wet
    wa
    wph
    wps
    wch
    wth
    wta
    wa
    #
    wa
    wa
    #
    wa
    #
    wet
    wa
    wph
    wps
    wa
    #
    @1
    wa
    #
    @2
    wa
    #
    wet
    wa
    @15
    @3
    wa
    #
    wet
    wa
    #
    @9
    @5
    @17
    @18
    wet
    @15
    @1
    @2
    anass
    anbi1i
    @8
    @17
    wet
    @7
    @16
    @2
    wph
    wps
    wth
    anandi
    anbi1i
    anbi1i
    @5
    @15
    wet
    wa
    #
    @3
    wa
    #
    wet
    @15
    wa
    #
    @3
    wa
    #
    @19
    wph
    @0
    wa
    #
    @3
    wa
    wph
    @4
    wa
    @21
    @5
    wph
    @0
    @3
    anass
    @20
    @24
    @3
    wph
    wps
    wet
    anass
    anbi1i
    @4
    wph
    ancom
    3bitr4ri
    @20
    @22
    @3
    @15
    wet
    ancom
    anbi1i
    @23
    wet
    @18
    wa
    @19
    wet
    @15
    @3
    anass
    wet
    @18
    ancom
    bitri
    3bitri
    3bitr4ri
    @8
    @11
    wet
    wph
    @6
    @2
    anass
    anbi1i
    @11
    @14
    wet
    @10
    @13
    wph
    @10
    wps
    wch
    wa
    @12
    wa
    @13
    wps
    wth
    wch
    wta
    an4
    wps
    wch
    @12
    anass
    bitri
    anbi2i
    anbi1i
    3bitri
end
