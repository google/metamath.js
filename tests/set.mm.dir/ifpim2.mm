include "wn.mm"
include "wo.mm"
include "wtru.mm"
include "wa.mm"
include "wi.mm"
include "wif.mm"
include "tru.mm"
include "olci.mm"
include "biantrur.mm"
include "imor.mm"
include "orcom.mm"
include "bitri.mm"
include "dfifp4.mm"
include "3bitr4i.mm"

theorem ifpim2
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) <-> if- ( ps , T. , -. ph ) )

  proof
    wps
    wph
    wn
    #
    wo
    #
    wps
    wn
    #
    wtru
    wo
    #
    @1
    wa
    wph
    wps
    wi
    #
    wps
    wtru
    @0
    wif
    @3
    @1
    wtru
    @2
    tru
    olci
    biantrur
    @4
    @0
    wps
    wo
    @1
    wph
    wps
    imor
    @0
    wps
    orcom
    bitri
    wps
    wtru
    @0
    dfifp4
    3bitr4i
end
