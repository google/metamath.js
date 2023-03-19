include "wi.mm"
include "wn.mm"
include "idd.mm"
include "con3.mm"
include "jad.mm"

theorem pm2.65
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) -> ( ( ph -> -. ps ) -> -. ph ) )

  proof
    wph
    wps
    wi
    #
    wph
    wps
    wn
    wph
    wn
    #
    @0
    @1
    idd
    wph
    wps
    con3
    jad
end
