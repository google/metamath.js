include "wfun.mm"
include "ccom.mm"
include "wceq.mm"
include "crn.mm"
include "cres.mm"
include "ccnv.mm"
include "cid.mm"
include "funcocnv2.mm"
include "coeq2d.mm"
include "coass.mm"
include "eqcomi.mm"
include "coires1.mm"
include "3eqtr3g.mm"
include "coeq1.mm"
include "sylan9req.mm"

theorem funcoeqres
  let cF: class F
  let cG: class G
  let cH: class H


  assert |- ( ( Fun G /\ ( F o. G ) = H ) -> ( F |` ran G ) = ( H o. `' G ) )

  proof
    cG
    wfun
    #
    cF
    cG
    ccom
    #
    cH
    wceq
    cF
    cG
    crn
    #
    cres
    #
    @1
    cG
    ccnv
    #
    ccom
    #
    cH
    @4
    ccom
    @0
    cF
    cG
    @4
    ccom
    #
    ccom
    #
    cF
    cid
    @2
    cres
    #
    ccom
    @5
    @3
    @0
    @6
    @8
    cF
    cG
    funcocnv2
    coeq2d
    @5
    @7
    cF
    cG
    @4
    coass
    eqcomi
    cF
    @2
    coires1
    3eqtr3g
    @1
    cH
    @4
    coeq1
    sylan9req
end
