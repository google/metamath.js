include "wn.mm"
include "wa.mm"
include "adantlr.mm"
include "anassrs.mm"
include "pm2.61dan.mm"

theorem pm2.61ddan
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume pm2.61ddan.1: |- ( ( ph /\ ps ) -> th )
  assume pm2.61ddan.2: |- ( ( ph /\ ch ) -> th )
  assume pm2.61ddan.3: |- ( ( ph /\ ( -. ps /\ -. ch ) ) -> th )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wth
    pm2.61ddan.1
    wph
    wps
    wn
    #
    wa
    wch
    wth
    wph
    wch
    wth
    @0
    pm2.61ddan.2
    adantlr
    wph
    @0
    wch
    wn
    wth
    pm2.61ddan.3
    anassrs
    pm2.61dan
    pm2.61dan
end
