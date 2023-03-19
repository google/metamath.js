include "wa.mm"
include "w3a.mm"
include "anbi12i.mm"
include "df-3an.mm"
include "3bitr4i.mm"

theorem 3anbi123i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume bi3.1: |- ( ph <-> ps )
  assume bi3.2: |- ( ch <-> th )
  assume bi3.3: |- ( ta <-> et )


  assert |- ( ( ph /\ ch /\ ta ) <-> ( ps /\ th /\ et ) )

  proof
    wph
    wch
    wa
    #
    wta
    wa
    wps
    wth
    wa
    #
    wet
    wa
    wph
    wch
    wta
    w3a
    wps
    wth
    wet
    w3a
    @0
    @1
    wta
    wet
    wph
    wps
    wch
    wth
    bi3.1
    bi3.2
    anbi12i
    bi3.3
    anbi12i
    wph
    wch
    wta
    df-3an
    wps
    wth
    wet
    df-3an
    3bitr4i
end
