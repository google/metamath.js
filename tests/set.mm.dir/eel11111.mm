include "wi.mm"
include "wa.mm"
include "exp41.mm"
include "ex.mm"
include "syl3c.mm"
include "mp2d.mm"

theorem eel11111
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume eel11111.1: |- ( ph -> ps )
  assume eel11111.2: |- ( ph -> ch )
  assume eel11111.3: |- ( ph -> th )
  assume eel11111.4: |- ( ph -> ta )
  assume eel11111.5: |- ( ph -> et )
  assume eel11111.6: |- ( ( ( ( ( ps /\ ch ) /\ th ) /\ ta ) /\ et ) -> ze )


  assert |- ( ph -> ze )

  proof
    wph
    wta
    wet
    wze
    eel11111.4
    eel11111.5
    wph
    wps
    wch
    wth
    wta
    wet
    wze
    wi
    wi
    #
    eel11111.1
    eel11111.2
    eel11111.3
    wps
    wch
    wth
    @0
    wi
    wps
    wch
    wa
    wth
    wta
    wet
    wze
    eel11111.6
    exp41
    ex
    syl3c
    mp2d
end
