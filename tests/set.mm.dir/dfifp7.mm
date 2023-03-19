include "wa.mm"
include "wi.mm"
include "wn.mm"
include "wo.mm"
include "wif.mm"
include "orcom.mm"
include "dfifp6.mm"
include "imor.mm"
include "3bitr4i.mm"

theorem dfifp7
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( if- ( ph , ps , ch ) <-> ( ( ch -> ph ) -> ( ph /\ ps ) ) )

  proof
    wph
    wps
    wa
    #
    wch
    wph
    wi
    #
    wn
    #
    wo
    @2
    @0
    wo
    wph
    wps
    wch
    wif
    @1
    @0
    wi
    @0
    @2
    orcom
    wph
    wps
    wch
    dfifp6
    @1
    @0
    imor
    3bitr4i
end
