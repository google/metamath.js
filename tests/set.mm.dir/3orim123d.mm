include "wo.mm"
include "w3o.mm"
include "orim12d.mm"
include "df-3or.mm"
include "3imtr4g.mm"

theorem 3orim123d
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


  assert |- ( ph -> ( ( ps \/ th \/ et ) -> ( ch \/ ta \/ ze ) ) )

  proof
    wph
    wps
    wth
    wo
    #
    wet
    wo
    wch
    wta
    wo
    #
    wze
    wo
    wps
    wth
    wet
    w3o
    wch
    wta
    wze
    w3o
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
    orim12d
    3anim123d.3
    orim12d
    wps
    wth
    wet
    df-3or
    wch
    wta
    wze
    df-3or
    3imtr4g
end
