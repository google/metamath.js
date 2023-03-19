include "w3a.mm"
include "wa.mm"
include "3anass.mm"
include "3anan12.mm"
include "3anrev.mm"
include "bitri.mm"
include "3anbi123i.mm"
include "3an6.mm"
include "an4.mm"
include "anbi2i.mm"
include "3bitr4i.mm"
include "anbi1i.mm"
include "df-3an.mm"
include "3ancomb.mm"
include "3bitri.mm"

theorem an33rean
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh


  assert |- ( ( ( ph /\ ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ( ze /\ si /\ rh ) ) <-> ( ( ph /\ ta /\ rh ) /\ ( ( ps /\ th ) /\ ( et /\ si ) /\ ( ch /\ ze ) ) ) )

  proof
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
    wze
    wsi
    wrh
    w3a
    #
    w3a
    wph
    wps
    wch
    wa
    #
    wa
    #
    wta
    wth
    wet
    wa
    #
    wa
    #
    wrh
    wsi
    wze
    wa
    #
    wa
    #
    w3a
    wph
    wta
    wrh
    w3a
    #
    @3
    @5
    @7
    w3a
    #
    wa
    @9
    wps
    wth
    wa
    #
    wet
    wsi
    wa
    wch
    wze
    wa
    w3a
    #
    wa
    @0
    @4
    @1
    @6
    @2
    @8
    wph
    wps
    wch
    3anass
    wth
    wta
    wet
    3anan12
    @2
    wrh
    wsi
    wze
    w3a
    @8
    wze
    wsi
    wrh
    3anrev
    wrh
    wsi
    wze
    3anass
    bitri
    3anbi123i
    wph
    @3
    wta
    @5
    wrh
    @7
    3an6
    @10
    @12
    @9
    @10
    @3
    wth
    wsi
    wa
    #
    wet
    wze
    wa
    #
    w3a
    #
    @11
    wch
    wsi
    wa
    #
    @14
    w3a
    #
    @12
    @3
    @5
    @7
    wa
    #
    wa
    @3
    @13
    @14
    wa
    #
    wa
    @10
    @15
    @18
    @19
    @3
    wth
    wet
    wsi
    wze
    an4
    anbi2i
    @3
    @5
    @7
    3anass
    @3
    @13
    @14
    3anass
    3bitr4i
    @3
    @13
    wa
    #
    @14
    wa
    @11
    @16
    wa
    #
    @14
    wa
    @15
    @17
    @20
    @21
    @14
    wps
    wch
    wth
    wsi
    an4
    anbi1i
    @3
    @13
    @14
    df-3an
    @11
    @16
    @14
    df-3an
    3bitr4i
    wps
    wch
    wet
    w3a
    #
    wth
    wsi
    wze
    w3a
    #
    wa
    wps
    wet
    wch
    w3a
    #
    @23
    wa
    @17
    @12
    @22
    @24
    @23
    wps
    wch
    wet
    3ancomb
    anbi1i
    wps
    wth
    wch
    wsi
    wet
    wze
    3an6
    wps
    wth
    wet
    wsi
    wch
    wze
    3an6
    3bitr4i
    3bitri
    anbi2i
    3bitri
end
