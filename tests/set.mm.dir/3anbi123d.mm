include "wa.mm"
include "w3a.mm"
include "anbi12d.mm"
include "df-3an.mm"
include "3bitr4g.mm"

theorem 3anbi123d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume bi3d.1: |- ( ph -> ( ps <-> ch ) )
  assume bi3d.2: |- ( ph -> ( th <-> ta ) )
  assume bi3d.3: |- ( ph -> ( et <-> ze ) )


  assert |- ( ph -> ( ( ps /\ th /\ et ) <-> ( ch /\ ta /\ ze ) ) )

  proof
    wph
    wps
    wth
    wa
    #
    wet
    wa
    wch
    wta
    wa
    #
    wze
    wa
    wps
    wth
    wet
    w3a
    wch
    wta
    wze
    w3a
    wph
    @0
    @1
    wet
    wze
    wph
    wps
    wch
    wth
    wta
    bi3d.1
    bi3d.2
    anbi12d
    bi3d.3
    anbi12d
    wps
    wth
    wet
    df-3an
    wch
    wta
    wze
    df-3an
    3bitr4g
end
