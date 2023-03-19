include "cclm.mm"
include "wcel.mm"
include "clmod.mm"
include "ccnfld.mm"
include "cress.mm"
include "co.mm"
include "wceq.mm"
include "csubrg.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "cbs.mm"
include "wsbc.mm"
include "csca.mm"
include "cvv.mm"
include "fvexd.mm"
include "id.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "sylan9eqr.mm"
include "adantr.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "sbcied.mm"
include "df-clm.mm"
include "elrab2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem isclm
  let cF: class F
  let cK: class K
  let cW: class W
  let vf: setvar f
  let vk: setvar k
  let vw: setvar w
  assume isclm.f: |- F = ( Scalar ` W )
  assume isclm.k: |- K = ( Base ` F )


  assert |- ( W e. CMod <-> ( W e. LMod /\ F = ( CCfld |`s K ) /\ K e. ( SubRing ` CCfld ) ) )

  proof
    cW
    cclm
    wcel
    cW
    clmod
    wcel
    #
    cF
    ccnfld
    cK
    cress
    co
    #
    wceq
    #
    cK
    ccnfld
    csubrg
    cfv
    #
    wcel
    #
    wa
    #
    wa
    @0
    @2
    @4
    w3a
    vf
    cv
    #
    ccnfld
    vk
    cv
    #
    cress
    co
    #
    wceq
    #
    @7
    @3
    wcel
    #
    wa
    #
    vk
    @6
    cbs
    cfv
    #
    wsbc
    #
    vf
    vw
    cv
    #
    csca
    cfv
    #
    wsbc
    @5
    vw
    cW
    clmod
    cclm
    @14
    cW
    wceq
    #
    @13
    @5
    vf
    @15
    cvv
    @16
    @14
    csca
    fvexd
    @16
    @6
    @15
    wceq
    #
    wa
    #
    @11
    @5
    vk
    @12
    cvv
    @18
    @6
    cbs
    fvexd
    @18
    @7
    @12
    wceq
    #
    wa
    #
    @9
    @2
    @10
    @4
    @20
    @6
    cF
    @8
    @1
    @18
    @6
    cF
    wceq
    @19
    @17
    @16
    @6
    @15
    cF
    @17
    id
    @16
    @15
    cW
    csca
    cfv
    cF
    @14
    cW
    csca
    fveq2
    isclm.f
    syl6eqr
    sylan9eqr
    #
    adantr
    @20
    @7
    cK
    ccnfld
    cress
    @19
    @18
    @7
    @12
    cK
    @19
    id
    @18
    @12
    cF
    cbs
    cfv
    cK
    @18
    @6
    cF
    cbs
    @21
    fveq2d
    isclm.k
    syl6eqr
    sylan9eqr
    #
    oveq2d
    eqeq12d
    @20
    @7
    cK
    @3
    @22
    eleq1d
    anbi12d
    sbcied
    sbcied
    vw
    vf
    vk
    df-clm
    elrab2
    @0
    @2
    @4
    3anass
    bitr4i
end
