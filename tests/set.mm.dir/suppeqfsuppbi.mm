include "cvv.mm"
include "wcel.mm"
include "wfun.mm"
include "wa.mm"
include "csupp.mm"
include "co.mm"
include "wceq.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wb.mm"
include "wi.mm"
include "cfn.mm"
include "simprlr.mm"
include "simprll.mm"
include "simpl.mm"
include "funisfsupp.mm"
include "syl3anc.mm"
include "adantr.mm"
include "simpr.mm"
include "ex.mm"
include "adantl.mm"
include "impcom.mm"
include "eleq1.mm"
include "bicomd.mm"
include "sylan9bb.mm"
include "bitr4d.mm"
include "exp31.mm"
include "wn.mm"
include "relfsupp.mm"
include "brrelex2i.mm"
include "pm5.21ni.mm"
include "2a1d.mm"
include "pm2.61i.mm"

theorem suppeqfsuppbi
  let cU: class U
  let cF: class F
  let cG: class G
  let cV: class V
  let cZ: class Z


  assert |- ( ( ( F e. U /\ Fun F ) /\ ( G e. V /\ Fun G ) ) -> ( ( F supp Z ) = ( G supp Z ) -> ( F finSupp Z <-> G finSupp Z ) ) )

  proof
    cZ
    cvv
    wcel
    #
    cF
    cU
    wcel
    #
    cF
    wfun
    #
    wa
    #
    cG
    cV
    wcel
    #
    cG
    wfun
    #
    wa
    #
    wa
    #
    cF
    cZ
    csupp
    co
    #
    cG
    cZ
    csupp
    co
    #
    wceq
    #
    cF
    cZ
    cfsupp
    wbr
    #
    cG
    cZ
    cfsupp
    wbr
    #
    wb
    #
    wi
    wi
    @0
    @7
    @10
    @13
    @0
    @7
    wa
    #
    @10
    wa
    @11
    @8
    cfn
    wcel
    #
    @12
    @14
    @11
    @15
    wb
    #
    @10
    @14
    @2
    @1
    @0
    @16
    @0
    @1
    @2
    @6
    simprlr
    @0
    @1
    @2
    @6
    simprll
    @0
    @7
    simpl
    cF
    cU
    cvv
    cZ
    funisfsupp
    syl3anc
    adantr
    @14
    @12
    @9
    cfn
    wcel
    #
    @10
    @15
    @7
    @0
    @12
    @17
    wb
    #
    @6
    @0
    @18
    wi
    @3
    @6
    @0
    @18
    @6
    @0
    wa
    @5
    @4
    @0
    @18
    @6
    @5
    @0
    @4
    @5
    simpr
    adantr
    @6
    @4
    @0
    @4
    @5
    simpl
    adantr
    @6
    @0
    simpr
    cG
    cV
    cvv
    cZ
    funisfsupp
    syl3anc
    ex
    adantl
    impcom
    @10
    @15
    @17
    @8
    @9
    cfn
    eleq1
    bicomd
    sylan9bb
    bitr4d
    exp31
    @0
    wn
    @13
    @7
    @10
    @11
    @0
    @12
    cF
    cZ
    cfsupp
    relfsupp
    brrelex2i
    cG
    cZ
    cfsupp
    relfsupp
    brrelex2i
    pm5.21ni
    2a1d
    pm2.61i
end
