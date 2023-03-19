include "cc.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cdif.mm"
include "wcel.mm"
include "crp.mm"
include "cz.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "clogb.mm"
include "ccxp.mm"
include "cmul.mm"
include "wceq.mm"
include "wa.mm"
include "rpcn.mm"
include "adantr.mm"
include "wne.mm"
include "rpne0.mm"
include "simpr.mm"
include "cxpexpzd.mm"
include "3adant1.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "cr.mm"
include "zre.mm"
include "relogbreexp.mm"
include "syl3an3.mm"
include "eqtrd.mm"

theorem relogbzexp
  let cB: class B
  let cC: class C
  let cN: class N


  assert |- ( ( B e. ( CC \ { 0 , 1 } ) /\ C e. RR+ /\ N e. ZZ ) -> ( B logb ( C ^ N ) ) = ( N x. ( B logb C ) ) )

  proof
    cB
    cc
    cc0
    c1
    cpr
    cdif
    wcel
    #
    cC
    crp
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cB
    cC
    cN
    cexp
    co
    #
    clogb
    co
    cB
    cC
    cN
    ccxp
    co
    #
    clogb
    co
    #
    cN
    cB
    cC
    clogb
    co
    cmul
    co
    #
    @3
    @4
    @5
    cB
    clogb
    @3
    @5
    @4
    @1
    @2
    @5
    @4
    wceq
    @0
    @1
    @2
    wa
    cC
    cN
    @1
    cC
    cc
    wcel
    @2
    cC
    rpcn
    adantr
    @1
    cC
    cc0
    wne
    @2
    cC
    rpne0
    adantr
    @1
    @2
    simpr
    cxpexpzd
    3adant1
    eqcomd
    oveq2d
    @2
    @0
    @1
    cN
    cr
    wcel
    @6
    @7
    wceq
    cN
    zre
    cB
    cC
    cN
    relogbreexp
    syl3an3
    eqtrd
end
