include "cfld.mm"
include "wcel.mm"
include "cdrng.mm"
include "ccring.mm"
include "wa.mm"
include "flddivrng.mm"
include "fldcrng.mm"
include "jca.mm"
include "ccm2.mm"
include "crngo.mm"
include "iscrngo.mm"
include "simprbi.mm"
include "cin.mm"
include "elin.mm"
include "biimpri.mm"
include "df-fld.mm"
include "syl6eleqr.mm"
include "sylan2.mm"
include "impbii.mm"

theorem isfld2
  let cK: class K


  assert |- ( K e. Fld <-> ( K e. DivRingOps /\ K e. CRingOps ) )

  proof
    cK
    cfld
    wcel
    #
    cK
    cdrng
    wcel
    #
    cK
    ccring
    wcel
    #
    wa
    @0
    @1
    @2
    cK
    flddivrng
    cK
    fldcrng
    jca
    @2
    @1
    cK
    ccm2
    wcel
    #
    @0
    @2
    cK
    crngo
    wcel
    @3
    cK
    iscrngo
    simprbi
    @1
    @3
    wa
    #
    cK
    cdrng
    ccm2
    cin
    #
    cfld
    cK
    @5
    wcel
    @4
    cK
    cdrng
    ccm2
    elin
    biimpri
    df-fld
    syl6eleqr
    sylan2
    impbii
end
