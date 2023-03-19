include "wi.mm"
include "wa.mm"
include "3exp.mm"
include "syl.mm"
include "syl5.mm"
include "syl7.mm"
include "ex.mm"
include "pm2.43d.mm"
include "imp.mm"

theorem eel2122old
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume eel2122old.1: |- ( ( ph /\ ps ) -> ch )
  assume eel2122old.2: |- ( ps -> th )
  assume eel2122old.3: |- ( ps -> ta )
  assume eel2122old.4: |- ( ( ch /\ th /\ ta ) -> et )


  assert |- ( ( ph /\ ps ) -> et )

  proof
    wph
    wps
    wet
    wph
    wps
    wet
    wph
    wps
    wps
    wet
    wi
    #
    wph
    wps
    wps
    @0
    wi
    wps
    wta
    wph
    wps
    wa
    #
    wps
    wet
    eel2122old.3
    wps
    wth
    @1
    wta
    wet
    wi
    #
    eel2122old.2
    @1
    wch
    wth
    @2
    wi
    eel2122old.1
    wch
    wth
    wta
    wet
    eel2122old.4
    3exp
    syl
    syl5
    syl7
    ex
    pm2.43d
    pm2.43d
    imp
end
