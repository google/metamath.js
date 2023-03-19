include "wi.mm"
include "expd.mm"
include "syld.mm"
include "impd.mm"

theorem syland
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
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
