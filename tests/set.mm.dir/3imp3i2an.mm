include "wi.mm"
include "wa.mm"
include "3exp.mm"
include "ex.mm"
include "syl8.mm"
include "com4r.mm"
include "syl.mm"
include "pm2.43b.mm"
include "pm2.43i.mm"
include "3imp231.mm"

theorem 3imp3i2an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume 3imp3i2an.1: |- ( ( ph /\ ps /\ ch ) -> th )
  assume 3imp3i2an.2: |- ( ( ph /\ ch ) -> ta )
  assume 3imp3i2an.3: |- ( ( th /\ ta ) -> et )


  assert |- ( ( ph /\ ps /\ ch ) -> et )

  proof
    wch
    wph
    wps
    wet
    wch
    wph
    wps
    wet
    wi
    wi
    wch
    wph
    wps
    wch
    wet
    wch
    wph
    wps
    wch
    wet
    wi
    wi
    #
    wph
    wch
    wph
    @0
    wi
    #
    wph
    wch
    wa
    wta
    @1
    3imp3i2an.2
    wph
    wps
    wch
    wta
    wet
    wph
    wps
    wch
    wth
    wta
    wet
    wi
    wph
    wps
    wch
    wth
    3imp3i2an.1
    3exp
    wth
    wta
    wet
    3imp3i2an.3
    ex
    syl8
    com4r
    syl
    ex
    pm2.43b
    com4r
    pm2.43i
    3imp231
end
