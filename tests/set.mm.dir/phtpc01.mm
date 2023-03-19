include "cphtpc.mm"
include "cfv.mm"
include "wbr.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "cphtpy.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "isphtpc.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "phtpy01.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "3impia.mm"
include "sylbi.mm"

theorem phtpc01
  let cF: class F
  let cG: class G
  let cJ: class J
  let vh: setvar h


  assert |- ( F ( ~=ph ` J ) G -> ( ( F ` 0 ) = ( G ` 0 ) /\ ( F ` 1 ) = ( G ` 1 ) ) )

  proof
    cF
    cG
    cJ
    cphtpc
    cfv
    wbr
    cF
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    cG
    @0
    wcel
    #
    cF
    cG
    cJ
    cphtpy
    cfv
    co
    #
    c0
    wne
    #
    w3a
    cc0
    cF
    cfv
    cc0
    cG
    cfv
    wceq
    c1
    cF
    cfv
    c1
    cG
    cfv
    wceq
    wa
    #
    cF
    cG
    cJ
    isphtpc
    @1
    @2
    @4
    @5
    @4
    vh
    cv
    #
    @3
    wcel
    #
    vh
    wex
    @1
    @2
    wa
    #
    @5
    vh
    @3
    n0
    @8
    @7
    @5
    vh
    @8
    @7
    @5
    @8
    @7
    wa
    cF
    cG
    @6
    cJ
    @1
    @2
    @7
    simpll
    @1
    @2
    @7
    simplr
    @8
    @7
    simpr
    phtpy01
    ex
    exlimdv
    syl5bi
    3impia
    sylbi
end
