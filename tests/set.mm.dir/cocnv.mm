include "wfun.mm"
include "wa.mm"
include "ccom.mm"
include "ccnv.mm"
include "crn.mm"
include "cres.mm"
include "coass.mm"
include "cid.mm"
include "wceq.mm"
include "funcocnv2.mm"
include "adantl.mm"
include "coeq2d.mm"
include "resco.mm"
include "wrel.mm"
include "funrel.mm"
include "coi1.mm"
include "syl.mm"
include "reseq1d.mm"
include "adantr.mm"
include "syl5eqr.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem cocnv
  let cF: class F
  let cG: class G


  assert |- ( ( Fun F /\ Fun G ) -> ( ( F o. G ) o. `' G ) = ( F |` ran G ) )

  proof
    cF
    wfun
    #
    cG
    wfun
    #
    wa
    #
    cF
    cG
    ccom
    cG
    ccnv
    #
    ccom
    cF
    cG
    @3
    ccom
    #
    ccom
    #
    cF
    cG
    crn
    #
    cres
    #
    cF
    cG
    @3
    coass
    @2
    @5
    cF
    cid
    @6
    cres
    #
    ccom
    #
    @7
    @2
    @4
    @8
    cF
    @1
    @4
    @8
    wceq
    @0
    cG
    funcocnv2
    adantl
    coeq2d
    @2
    @9
    cF
    cid
    ccom
    #
    @6
    cres
    #
    @7
    cF
    cid
    @6
    resco
    @0
    @11
    @7
    wceq
    @1
    @0
    @10
    cF
    @6
    @0
    cF
    wrel
    @10
    cF
    wceq
    cF
    funrel
    cF
    coi1
    syl
    reseq1d
    adantr
    syl5eqr
    eqtrd
    syl5eq
end
