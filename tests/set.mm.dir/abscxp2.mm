include "cc.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "ccxp.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "0red.mm"
include "0le0.mm"
include "a1i.mm"
include "simplr.mm"
include "recxpcl.mm"
include "syl3anc.mm"
include "cxpge0.mm"
include "absidd.mm"
include "simpr.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "abs00bd.mm"
include "3eqtr4d.mm"
include "wne.mm"
include "clog.mm"
include "cmul.mm"
include "ce.mm"
include "cre.mm"
include "recnd.mm"
include "logcl.mm"
include "adantlr.mm"
include "mulcld.mm"
include "absef.mm"
include "syl.mm"
include "remul2d.mm"
include "relog.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "simpll.mm"
include "cxpef.mm"
include "abscld.mm"
include "wb.mm"
include "abs00.mm"
include "adantr.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "pm2.61dane.mm"

theorem abscxp2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. RR ) -> ( abs ` ( A ^c B ) ) = ( ( abs ` A ) ^c B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    ccxp
    co
    #
    cabs
    cfv
    #
    cA
    cabs
    cfv
    #
    cB
    ccxp
    co
    #
    wceq
    cA
    cc0
    @2
    cA
    cc0
    wceq
    #
    wa
    #
    cc0
    cB
    ccxp
    co
    #
    cabs
    cfv
    @9
    @4
    @6
    @8
    @9
    @8
    cc0
    cr
    wcel
    #
    cc0
    cc0
    cle
    wbr
    #
    @1
    @9
    cr
    wcel
    @8
    0red
    #
    @11
    @8
    0le0
    a1i
    #
    @0
    @1
    @7
    simplr
    #
    cc0
    cB
    recxpcl
    syl3anc
    @8
    @10
    @11
    @1
    cc0
    @9
    cle
    wbr
    @12
    @13
    @14
    cc0
    cB
    cxpge0
    syl3anc
    absidd
    @8
    @3
    @9
    cabs
    @8
    cA
    cc0
    cB
    ccxp
    @2
    @7
    simpr
    #
    oveq1d
    fveq2d
    @8
    @5
    cc0
    cB
    ccxp
    @8
    cA
    @15
    abs00bd
    oveq1d
    3eqtr4d
    @2
    cA
    cc0
    wne
    #
    wa
    #
    cB
    cA
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cabs
    cfv
    #
    cB
    @5
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    @4
    @6
    @17
    @21
    @19
    cre
    cfv
    #
    ce
    cfv
    #
    @24
    @17
    @19
    cc
    wcel
    @21
    @26
    wceq
    @17
    cB
    @18
    @17
    cB
    @0
    @1
    @16
    simplr
    #
    recnd
    #
    @0
    @16
    @18
    cc
    wcel
    @1
    cA
    logcl
    adantlr
    #
    mulcld
    @19
    absef
    syl
    @17
    @25
    @23
    ce
    @17
    @25
    cB
    @18
    cre
    cfv
    #
    cmul
    co
    @23
    @17
    cB
    @18
    @27
    @29
    remul2d
    @17
    @30
    @22
    cB
    cmul
    @0
    @16
    @30
    @22
    wceq
    @1
    cA
    relog
    adantlr
    oveq2d
    eqtrd
    fveq2d
    eqtrd
    @17
    @3
    @20
    cabs
    @17
    @0
    @16
    cB
    cc
    wcel
    #
    @3
    @20
    wceq
    @0
    @1
    @16
    simpll
    #
    @2
    @16
    simpr
    @28
    cA
    cB
    cxpef
    syl3anc
    fveq2d
    @17
    @5
    cc
    wcel
    @5
    cc0
    wne
    #
    @31
    @6
    @24
    wceq
    @17
    @5
    @17
    cA
    @32
    abscld
    recnd
    @2
    @33
    @16
    @2
    @5
    cc0
    cA
    cc0
    @0
    @5
    cc0
    wceq
    @7
    wb
    @1
    cA
    abs00
    adantr
    necon3bid
    biimpar
    @28
    @5
    cB
    cxpef
    syl3anc
    3eqtr4d
    pm2.61dane
end
