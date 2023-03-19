include "wo.mm"
include "w3o.mm"
include "orbi12i.mm"
include "df-3or.mm"
include "3bitr4i.mm"

theorem 3orbi123i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume bi3.1: |- ( ph <-> ps )
  assume bi3.2: |- ( ch <-> th )
  assume bi3.3: |- ( ta <-> et )


  assert |- ( ( ph \/ ch \/ ta ) <-> ( ps \/ th \/ et ) )

  proof
    wph
    wch
    wo
    #
    wta
    wo
    wps
    wth
    wo
    #
    wet
    wo
    wph
    wch
    wta
    w3o
    wps
    wth
    wet
    w3o
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
    orbi12i
    bi3.3
    orbi12i
    wph
    wch
    wta
    df-3or
    wps
    wth
    wet
    df-3or
    3bitr4i
end
