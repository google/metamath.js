include "wo.mm"
include "wn.mm"
include "wa.mm"
include "wif.mm"
include "pm2.1.mm"
include "biantrur.mm"
include "dfifp4.mm"
include "bitr4i.mm"

theorem ifpdfor2
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/ ps ) <-> if- ( ph , ph , ps ) )

  proof
    wph
    wps
    wo
    #
    wph
    wn
    wph
    wo
    #
    @0
    wa
    wph
    wph
    wps
    wif
    @1
    @0
    wph
    pm2.1
    biantrur
    wph
    wph
    wps
    dfifp4
    bitr4i
end
