include "wn.mm"
include "wo.mm"
include "orel2.mm"
include "jao1i.mm"
include "com12.mm"

theorem pm2.64
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/ ps ) -> ( ( ph \/ -. ps ) -> ph ) )

  proof
    wph
    wps
    wn
    #
    wo
    wph
    wps
    wo
    #
    wph
    wph
    @0
    @1
    wps
    wph
    orel2
    jao1i
    com12
end
