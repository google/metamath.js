include "clmod.mm"
include "wcel.mm"
include "ccnfld.mm"
include "cress.mm"
include "co.mm"
include "wceq.mm"
include "csubrg.mm"
include "cfv.mm"
include "w3a.mm"
include "cbs.mm"
include "cclm.mm"
include "simp1.mm"
include "simp2.mm"
include "eqid.mm"
include "subrgbas.mm"
include "3ad2ant3.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "simp3.mm"
include "eqeltrrd.mm"
include "isclm.mm"
include "syl3anbrc.mm"

theorem isclmi
  let cF: class F
  let cK: class K
  let cW: class W
  assume clm0.f: |- F = ( Scalar ` W )


  assert |- ( ( W e. LMod /\ F = ( CCfld |`s K ) /\ K e. ( SubRing ` CCfld ) ) -> W e. CMod )

  proof
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
    w3a
    #
    @0
    cF
    ccnfld
    cF
    cbs
    cfv
    #
    cress
    co
    #
    wceq
    @6
    @3
    wcel
    cW
    cclm
    wcel
    @0
    @2
    @4
    simp1
    @5
    cF
    @1
    @7
    @0
    @2
    @4
    simp2
    #
    @5
    cK
    @6
    ccnfld
    cress
    @5
    cK
    @1
    cbs
    cfv
    #
    @6
    @4
    @0
    cK
    @9
    wceq
    @2
    cK
    ccnfld
    @1
    @1
    eqid
    subrgbas
    3ad2ant3
    @5
    cF
    @1
    cbs
    @8
    fveq2d
    eqtr4d
    #
    oveq2d
    eqtrd
    @5
    cK
    @6
    @3
    @10
    @0
    @2
    @4
    simp3
    eqeltrrd
    cF
    @6
    cW
    clm0.f
    @6
    eqid
    isclm
    syl3anbrc
end
