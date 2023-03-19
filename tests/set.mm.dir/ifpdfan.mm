include "wa.mm"
include "wn.mm"
include "wfal.mm"
include "wo.mm"
include "wif.mm"
include "fal.mm"
include "intnan.mm"
include "biorfi.mm"
include "df-ifp.mm"
include "bitr4i.mm"

theorem ifpdfan
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph /\ ps ) <-> if- ( ph , ps , F. ) )

  proof
    wph
    wps
    wa
    #
    @0
    wph
    wn
    #
    wfal
    wa
    #
    wo
    wph
    wps
    wfal
    wif
    @2
    @0
    wfal
    @1
    fal
    intnan
    biorfi
    wph
    wps
    wfal
    df-ifp
    bitr4i
end
