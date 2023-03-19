include "wn.mm"
include "wfal.mm"
include "wo.mm"
include "wtru.mm"
include "wa.mm"
include "wif.mm"
include "tru.mm"
include "olci.mm"
include "biantru.mm"
include "fal.mm"
include "biorfi.mm"
include "dfifp4.mm"
include "3bitr4i.mm"

theorem ifpnot
  let wph: wff ph


  assert |- ( -. ph <-> if- ( ph , F. , T. ) )

  proof
    wph
    wn
    #
    wfal
    wo
    #
    @1
    wph
    wtru
    wo
    #
    wa
    @0
    wph
    wfal
    wtru
    wif
    @2
    @1
    wtru
    wph
    tru
    olci
    biantru
    wfal
    @0
    fal
    biorfi
    wph
    wfal
    wtru
    dfifp4
    3bitr4i
end
