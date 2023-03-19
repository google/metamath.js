include "cvol.mm"
include "cdm.mm"
include "cbrsiga.mm"
include "cmbfm.mm"
include "co.mm"
include "wcel.mm"
include "cuni.mm"
include "wf.mm"
include "cr.mm"
include "csiga.mm"
include "crn.mm"
include "wceq.mm"
include "cfv.mm"
include "wa.mm"
include "dmvlsiga.mm"
include "issgon.mm"
include "mpbi.mm"
include "simpli.mm"
include "a1i.mm"
include "brsigarn.mm"
include "id.mm"
include "mbfmf.mm"
include "simpri.mm"
include "feq23i.mm"
include "sylibr.mm"

theorem mbfmvolf
  let cF: class F


  assert |- ( F e. ( dom vol MblFnM BrSiga ) -> F : RR --> RR )

  proof
    cF
    cvol
    cdm
    #
    cbrsiga
    cmbfm
    co
    wcel
    #
    @0
    cuni
    #
    cbrsiga
    cuni
    #
    cF
    wf
    cr
    cr
    cF
    wf
    @1
    @0
    cbrsiga
    cF
    @0
    csiga
    crn
    cuni
    #
    wcel
    #
    @1
    @5
    cr
    @2
    wceq
    #
    @0
    cr
    csiga
    cfv
    #
    wcel
    @5
    @6
    wa
    dmvlsiga
    @0
    cr
    issgon
    mpbi
    #
    simpli
    a1i
    cbrsiga
    @4
    wcel
    #
    @1
    @9
    cr
    @3
    wceq
    #
    cbrsiga
    @7
    wcel
    @9
    @10
    wa
    brsigarn
    cbrsiga
    cr
    issgon
    mpbi
    #
    simpli
    a1i
    @1
    id
    mbfmf
    cr
    cr
    @2
    @3
    cF
    @5
    @6
    @8
    simpri
    @9
    @10
    @11
    simpri
    feq23i
    sylibr
end
