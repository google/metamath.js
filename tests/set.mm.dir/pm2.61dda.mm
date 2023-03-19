include "wa.mm"
include "anassrs.mm"
include "wn.mm"
include "adantlr.mm"
include "pm2.61dan.mm"

theorem pm2.61dda
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume pm2.61dda.1: |- ( ( ph /\ -. ps ) -> th )
  assume pm2.61dda.2: |- ( ( ph /\ -. ch ) -> th )
  assume pm2.61dda.3: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wth
    wph
    wps
    wa
    wch
    wth
    wph
    wps
    wch
    wth
    pm2.61dda.3
    anassrs
    wph
    wch
    wn
    wth
    wps
    pm2.61dda.2
    adantlr
    pm2.61dan
    pm2.61dda.1
    pm2.61dan
end
