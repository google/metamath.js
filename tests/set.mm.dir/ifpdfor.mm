include "wo.mm"
include "wn.mm"
include "wtru.mm"
include "wa.mm"
include "wif.mm"
include "tru.mm"
include "olci.mm"
include "biantrur.mm"
include "dfifp4.mm"
include "bitr4i.mm"

theorem ifpdfor
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/ ps ) <-> if- ( ph , T. , ps ) )

  proof
    wph
    wps
    wo
    #
    wph
    wn
    #
    wtru
    wo
    #
    @0
    wa
    wph
    wtru
    wps
    wif
    @2
    @0
    wtru
    @1
    tru
    olci
    biantrur
    wph
    wtru
    wps
    dfifp4
    bitr4i
end
