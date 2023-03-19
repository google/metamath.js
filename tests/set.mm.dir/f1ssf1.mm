include "wfun.mm"
include "ccnv.mm"
include "wss.mm"
include "wi.mm"
include "wa.mm"
include "cdm.mm"
include "cres.mm"
include "wceq.mm"
include "funssres.mm"
include "funres11.mm"
include "cnveq.mm"
include "funeqd.mm"
include "syl5ibr.mm"
include "eqcoms.mm"
include "syl.mm"
include "ex.mm"
include "com23.mm"
include "3imp.mm"

theorem f1ssf1
  let cF: class F
  let cG: class G


  assert |- ( ( Fun F /\ Fun `' F /\ G C_ F ) -> Fun `' G )

  proof
    cF
    wfun
    #
    cF
    ccnv
    wfun
    #
    cG
    cF
    wss
    #
    cG
    ccnv
    #
    wfun
    #
    @0
    @2
    @1
    @4
    @0
    @2
    @1
    @4
    wi
    #
    @0
    @2
    wa
    cF
    cG
    cdm
    #
    cres
    #
    cG
    wceq
    @5
    cF
    cG
    funssres
    @5
    cG
    @7
    @1
    @4
    cG
    @7
    wceq
    #
    @7
    ccnv
    #
    wfun
    @6
    cF
    funres11
    @8
    @3
    @9
    cG
    @7
    cnveq
    funeqd
    syl5ibr
    eqcoms
    syl
    ex
    com23
    3imp
end
