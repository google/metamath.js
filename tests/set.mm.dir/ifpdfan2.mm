include "wa.mm"
include "wi.mm"
include "wn.mm"
include "wo.mm"
include "wif.mm"
include "id.mm"
include "notnoti.mm"
include "biorfi.mm"
include "dfifp6.mm"
include "bitr4i.mm"

theorem ifpdfan2
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph /\ ps ) <-> if- ( ph , ps , ph ) )

  proof
    wph
    wps
    wa
    #
    @0
    wph
    wph
    wi
    #
    wn
    #
    wo
    wph
    wps
    wph
    wif
    @2
    @0
    @1
    wph
    id
    notnoti
    biorfi
    wph
    wps
    wph
    dfifp6
    bitr4i
end
