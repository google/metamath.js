include "wi.mm"
include "wa.mm"
include "3exp.mm"
include "syl2imc.mm"
include "ex.mm"
include "pm2.43b.mm"
include "com13.mm"
include "syl.mm"
include "3imp231.mm"

theorem eel12131
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume eel12131.1: |- ( ph -> ps )
  assume eel12131.2: |- ( ( ph /\ ch ) -> th )
  assume eel12131.3: |- ( ( ph /\ ta ) -> et )
  assume eel12131.4: |- ( ( ps /\ th /\ et ) -> ze )


  assert |- ( ( ph /\ ch /\ ta ) -> ze )

  proof
    wta
    wph
    wch
    wze
    wta
    wph
    wch
    wze
    wi
    #
    wph
    wta
    wph
    @0
    wi
    #
    wph
    wta
    wa
    wet
    @1
    eel12131.3
    wch
    wph
    wet
    wze
    wch
    wph
    wet
    wze
    wi
    #
    wph
    wch
    wph
    @2
    wi
    wph
    wps
    wph
    wch
    wa
    wth
    @2
    eel12131.1
    eel12131.2
    wps
    wth
    wet
    wze
    eel12131.4
    3exp
    syl2imc
    ex
    pm2.43b
    com13
    syl
    ex
    pm2.43b
    3imp231
end
