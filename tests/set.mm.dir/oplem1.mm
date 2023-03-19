include "wn.mm"
include "wa.mm"
include "notbii.mm"
include "ord.mm"
include "syl5bir.mm"
include "jcad.mm"
include "biimpar.mm"
include "syl6.mm"
include "pm2.18d.mm"
include "sylibr.mm"

theorem oplem1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume oplem1.1: |- ( ph -> ( ps \/ ch ) )
  assume oplem1.2: |- ( ph -> ( th \/ ta ) )
  assume oplem1.3: |- ( ps <-> th )
  assume oplem1.4: |- ( ch -> ( th <-> ta ) )


  assert |- ( ph -> ps )

  proof
    wph
    wth
    wps
    wph
    wth
    wph
    wth
    wn
    #
    wch
    wta
    wa
    wth
    wph
    @0
    wch
    wta
    @0
    wps
    wn
    wph
    wch
    wps
    wth
    oplem1.3
    notbii
    wph
    wps
    wch
    oplem1.1
    ord
    syl5bir
    wph
    wth
    wta
    oplem1.2
    ord
    jcad
    wch
    wth
    wta
    oplem1.4
    biimpar
    syl6
    pm2.18d
    oplem1.3
    sylibr
end
