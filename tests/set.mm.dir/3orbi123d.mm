include "wo.mm"
include "w3o.mm"
include "orbi12d.mm"
include "df-3or.mm"
include "3bitr4g.mm"

theorem 3orbi123d
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


  assert |- ( ph -> ( ( ps \/ th \/ et ) <-> ( ch \/ ta \/ ze ) ) )

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
    bi3d.1
    bi3d.2
    orbi12d
    bi3d.3
    orbi12d
    wps
    wth
    wet
    df-3or
    wch
    wta
    wze
    df-3or
    3bitr4g
end
