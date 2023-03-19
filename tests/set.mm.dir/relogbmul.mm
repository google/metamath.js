include "cc.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cdif.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "caddc.mm"
include "clogb.mm"
include "wceq.mm"
include "relogmul.mm"
include "adantl.mm"
include "oveq1d.mm"
include "wne.mm"
include "relogcl.mm"
include "recnd.mm"
include "adantr.mm"
include "w3a.mm"
include "eldifpr.mm"
include "3simpa.mm"
include "sylbi.mm"
include "logcl.mm"
include "syl.mm"
include "logccne0.mm"
include "jca.mm"
include "divdir.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "csn.mm"
include "rpcn.mm"
include "mulcl.mm"
include "syl2an.mm"
include "rpne0.mm"
include "mulne0d.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "logbval.mm"
include "sylan2.mm"
include "rpcndif0.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem relogbmul
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( B e. ( CC \ { 0 , 1 } ) /\ ( A e. RR+ /\ C e. RR+ ) ) -> ( B logb ( A x. C ) ) = ( ( B logb A ) + ( B logb C ) ) )

  proof
    cB
    cc
    cc0
    c1
    cpr
    cdif
    wcel
    #
    cA
    crp
    wcel
    #
    cC
    crp
    wcel
    #
    wa
    #
    wa
    #
    cA
    cC
    cmul
    co
    #
    clog
    cfv
    #
    cB
    clog
    cfv
    #
    cdiv
    co
    #
    cA
    clog
    cfv
    #
    @7
    cdiv
    co
    #
    cC
    clog
    cfv
    #
    @7
    cdiv
    co
    #
    caddc
    co
    #
    cB
    @5
    clogb
    co
    #
    cB
    cA
    clogb
    co
    #
    cB
    cC
    clogb
    co
    #
    caddc
    co
    @4
    @8
    @9
    @11
    caddc
    co
    #
    @7
    cdiv
    co
    #
    @13
    @4
    @6
    @17
    @7
    cdiv
    @3
    @6
    @17
    wceq
    @0
    cA
    cC
    relogmul
    adantl
    oveq1d
    @4
    @9
    cc
    wcel
    #
    @11
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    @7
    cc0
    wne
    #
    wa
    #
    @18
    @13
    wceq
    @3
    @19
    @0
    @1
    @19
    @2
    @1
    @9
    cA
    relogcl
    recnd
    adantr
    adantl
    @3
    @20
    @0
    @2
    @20
    @1
    @2
    @11
    cC
    relogcl
    recnd
    adantl
    adantl
    @0
    @23
    @3
    @0
    @21
    @22
    @0
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    @21
    @0
    @24
    @25
    cB
    c1
    wne
    #
    w3a
    #
    @26
    cB
    cc
    cc0
    c1
    eldifpr
    #
    @24
    @25
    @27
    3simpa
    sylbi
    cB
    logcl
    syl
    @0
    @28
    @22
    @29
    cB
    logccne0
    sylbi
    jca
    adantr
    @9
    @11
    @7
    divdir
    syl3anc
    eqtrd
    @3
    @0
    @5
    cc
    cc0
    csn
    cdif
    #
    wcel
    #
    @14
    @8
    wceq
    @3
    @5
    cc
    wcel
    #
    @5
    cc0
    wne
    @31
    @1
    cA
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    @32
    @2
    cA
    rpcn
    #
    cC
    rpcn
    #
    cA
    cC
    mulcl
    syl2an
    @3
    cA
    cC
    @1
    @33
    @2
    @35
    adantr
    @2
    @34
    @1
    @36
    adantl
    @1
    cA
    cc0
    wne
    @2
    cA
    rpne0
    adantr
    @2
    cC
    cc0
    wne
    @1
    cC
    rpne0
    adantl
    mulne0d
    @5
    cc
    cc0
    eldifsn
    sylanbrc
    cB
    @5
    logbval
    sylan2
    @4
    @15
    @10
    @16
    @12
    caddc
    @3
    @0
    cA
    @30
    wcel
    #
    @15
    @10
    wceq
    @1
    @37
    @2
    cA
    rpcndif0
    adantr
    cB
    cA
    logbval
    sylan2
    @3
    @0
    cC
    @30
    wcel
    #
    @16
    @12
    wceq
    @2
    @38
    @1
    cC
    rpcndif0
    adantl
    cB
    cC
    logbval
    sylan2
    oveq12d
    3eqtr4d
end
