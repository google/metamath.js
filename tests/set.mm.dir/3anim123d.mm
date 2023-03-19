include "wa.mm"
include "w3a.mm"
include "anim12d.mm"
include "df-3an.mm"
include "3imtr4g.mm"

theorem 3anim123d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume 3anim123d.1: |- ( ph -> ( ps -> ch ) )
  assume 3anim123d.2: |- ( ph -> ( th -> ta ) )
  assume 3anim123d.3: |- ( ph -> ( et -> ze ) )


  assert |- ( ph -> ( ( ps /\ th /\ et ) -> ( ch /\ ta /\ ze ) ) )

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
    3anim123d.1
    3anim123d.2
    anim12d
    3anim123d.3
    anim12d
    wps
    wth
    wet
    df-3an
    wch
    wta
    wze
    df-3an
    3imtr4g
end
