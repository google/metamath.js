include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cfv.mm"
include "cop.mm"
include "cun.mm"
include "wceq.mm"
include "wrel.mm"
include "funrel.mm"
include "resdmdfsn.mm"
include "syl.mm"
include "adantr.mm"
include "uneq1d.mm"
include "wfn.mm"
include "funfn.mm"
include "fnsnsplit.mm"
include "sylanb.mm"
include "eqtr4d.mm"

theorem funresdfunsn
  let cF: class F
  let cX: class X


  assert |- ( ( Fun F /\ X e. dom F ) -> ( ( F |` ( _V \ { X } ) ) u. { <. X , ( F ` X ) >. } ) = F )

  proof
    cF
    wfun
    #
    cX
    cF
    cdm
    #
    wcel
    #
    wa
    #
    cF
    cvv
    cX
    csn
    #
    cdif
    cres
    #
    cX
    cX
    cF
    cfv
    cop
    csn
    #
    cun
    cF
    @1
    @4
    cdif
    cres
    #
    @6
    cun
    #
    cF
    @3
    @5
    @7
    @6
    @0
    @5
    @7
    wceq
    #
    @2
    @0
    cF
    wrel
    @9
    cF
    funrel
    cF
    cX
    resdmdfsn
    syl
    adantr
    uneq1d
    @0
    cF
    @1
    wfn
    @2
    cF
    @8
    wceq
    cF
    funfn
    @1
    cF
    cX
    fnsnsplit
    sylanb
    eqtr4d
end
