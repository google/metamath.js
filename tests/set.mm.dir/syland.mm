include "wi.mm"
include "expd.mm"
include "syld.mm"
include "impd.mm"

theorem syland
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume syland.1: |- ( ph -> ( ps -> ch ) )
  assume syland.2: |- ( ph -> ( ( ch /\ th ) -> ta ) )


  assert |- ( ph -> ( ( ps /\ th ) -> ta ) )

  proof
    wph
    wps
    wth
    wta
    wph
    wps
    wch
    wth
    wta
    wi
    syland.1
    wph
    wch
    wth
    wta
    syland.2
    expd
    syld
    impd
end
