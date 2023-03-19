include "com.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cuni.mm"
include "c0.mm"
include "wceq.mm"
include "unieq.mm"
include "uni0.mm"
include "peano1.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "adantl.mm"
include "wne.mm"
include "simpll.mm"
include "con0.mm"
include "omsson.mm"
include "syl6ss.mm"
include "simplr.mm"
include "simpr.mm"
include "ordunifi.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "pm2.61dane.mm"

theorem nnunifi
  let cS: class S


  assert |- ( ( S C_ _om /\ S e. Fin ) -> U. S e. _om )

  proof
    cS
    com
    wss
    #
    cS
    cfn
    wcel
    #
    wa
    #
    cS
    cuni
    #
    com
    wcel
    #
    cS
    c0
    cS
    c0
    wceq
    #
    @4
    @2
    @5
    @3
    c0
    cuni
    #
    com
    cS
    c0
    unieq
    @6
    c0
    com
    uni0
    peano1
    eqeltri
    syl6eqel
    adantl
    @2
    cS
    c0
    wne
    #
    wa
    #
    cS
    com
    @3
    @0
    @1
    @7
    simpll
    #
    @8
    cS
    con0
    wss
    @1
    @7
    @3
    cS
    wcel
    @8
    cS
    com
    con0
    @9
    omsson
    syl6ss
    @0
    @1
    @7
    simplr
    @2
    @7
    simpr
    cS
    ordunifi
    syl3anc
    sseldd
    pm2.61dane
end
