include "wfal.mm"
include "wo.mm"
include "wn.mm"
include "wtru.mm"
include "wa.mm"
include "wif.mm"
include "tru.mm"
include "olci.mm"
include "biantrur.mm"
include "fal.mm"
include "biorfi.mm"
include "dfifp4.mm"
include "3bitr4i.mm"

theorem ifpid2
  let wph: wff ph


  assert |- ( ph <-> if- ( ph , T. , F. ) )

  proof
    wph
    wfal
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
    wph
    wtru
    wfal
    wif
    @2
    @0
    wtru
    @1
    tru
    olci
    biantrur
    wfal
    wph
    fal
    biorfi
    wph
    wtru
    wfal
    dfifp4
    3bitr4i
end
