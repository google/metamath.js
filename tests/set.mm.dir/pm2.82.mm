include "wo.mm"
include "wn.mm"
include "pm2.24.mm"
include "orim2d.mm"
include "jao1i.mm"
include "orim1d.mm"

theorem pm2.82
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph \/ ps ) \/ ch ) -> ( ( ( ph \/ -. ch ) \/ th ) -> ( ( ph \/ ps ) \/ th ) ) )

  proof
    wph
    wps
    wo
    #
    wch
    wo
    wph
    wch
    wn
    #
    wo
    #
    @0
    wth
    @0
    wch
    @2
    wch
    @1
    wps
    wph
    wch
    wps
    pm2.24
    orim2d
    jao1i
    orim1d
end
