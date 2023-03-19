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
include "dfifp4.mm"
include "3bitr4i.mm"

theorem ifpim1
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) <-> if- ( -. ph , T. , ps ) )

  proof
    wph
    wn
    #
    wps
    wo
    #
    @0
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
    @0
    wtru
    wps
    wif
    @3
    @1
    wtru
    @2
    tru
    olci
    biantrur
    wph
    wps
    imor
    @0
    wtru
    wps
    dfifp4
    3bitr4i
end
