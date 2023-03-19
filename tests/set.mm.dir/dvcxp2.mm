include "crp.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cmpt.mm"
include "cdv.mm"
include "ccxp.mm"
include "cr.mm"
include "cpr.mm"
include "cnelprrecn.mm"
include "a1i.mm"
include "wa.mm"
include "simpr.mm"
include "relogcl.mm"
include "adantr.mm"
include "recnd.mm"
include "mulcld.mm"
include "efcl.mm"
include "adantl.mm"
include "c1.mm"
include "mulcomd.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "1cnd.mm"
include "dvmptid.mm"
include "dvmptcmul.mm"
include "mulid1d.mm"
include "3eqtrd.mm"
include "dvef.mm"
include "wf.mm"
include "eff.mm"
include "feqmptd.mm"
include "eqcomd.mm"
include "3eqtr4a.mm"
include "fveq2.mm"
include "dvmptco.mm"
include "rpcn.mm"
include "cc0.mm"
include "wne.mm"
include "rpne0.mm"
include "cxpefd.mm"
include "cxpcld.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"

theorem dvcxp2
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A e. RR+ -> ( CC _D ( x e. CC |-> ( A ^c x ) ) ) = ( x e. CC |-> ( ( log ` A ) x. ( A ^c x ) ) ) )

  proof
    cA
    crp
    wcel
    #
    cc
    vx
    cc
    vx
    cv
    #
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
    cmpt
    #
    cdv
    co
    vx
    cc
    @4
    @2
    cmul
    co
    #
    cmpt
    cc
    vx
    cc
    cA
    @1
    ccxp
    co
    #
    cmpt
    #
    cdv
    co
    vx
    cc
    @2
    @7
    cmul
    co
    #
    cmpt
    @0
    vx
    vy
    @3
    @2
    vy
    cv
    #
    ce
    cfv
    #
    @11
    cc
    cc
    @4
    @4
    cr
    cc
    cc
    cc
    cc
    cr
    cc
    cpr
    wcel
    @0
    cnelprrecn
    a1i
    #
    @12
    @0
    @1
    cc
    wcel
    #
    wa
    #
    @1
    @2
    @0
    @13
    simpr
    #
    @14
    @2
    @0
    @2
    cr
    wcel
    @13
    cA
    relogcl
    #
    adantr
    #
    recnd
    #
    mulcld
    @17
    @10
    cc
    wcel
    @11
    cc
    wcel
    @0
    @10
    efcl
    adantl
    #
    @19
    @0
    cc
    vx
    cc
    @3
    cmpt
    #
    cdv
    co
    cc
    vx
    cc
    @2
    @1
    cmul
    co
    #
    cmpt
    #
    cdv
    co
    vx
    cc
    @2
    c1
    cmul
    co
    #
    cmpt
    vx
    cc
    @2
    cmpt
    @0
    @20
    @22
    cc
    cdv
    @0
    vx
    cc
    @3
    @21
    @14
    @1
    @2
    @15
    @18
    mulcomd
    mpteq2dva
    oveq2d
    @0
    vx
    @1
    c1
    @2
    cc
    cc
    cc
    @12
    @15
    @14
    1cnd
    @0
    vx
    cc
    @12
    dvmptid
    @0
    @2
    @16
    recnd
    dvmptcmul
    @0
    vx
    cc
    @23
    @2
    @14
    @2
    @18
    mulid1d
    mpteq2dva
    3eqtrd
    @0
    cc
    ce
    cdv
    co
    ce
    cc
    vy
    cc
    @11
    cmpt
    #
    cdv
    co
    @24
    dvef
    @0
    @24
    ce
    cc
    cdv
    @0
    ce
    @24
    @0
    vy
    cc
    cc
    ce
    cc
    cc
    ce
    wf
    @0
    eff
    a1i
    feqmptd
    eqcomd
    #
    oveq2d
    @25
    3eqtr4a
    @10
    @3
    ce
    fveq2
    #
    @26
    dvmptco
    @0
    @8
    @5
    cc
    cdv
    @0
    vx
    cc
    @7
    @4
    @14
    cA
    @1
    @0
    cA
    cc
    wcel
    @13
    cA
    rpcn
    adantr
    #
    @0
    cA
    cc0
    wne
    @13
    cA
    rpne0
    adantr
    @15
    cxpefd
    #
    mpteq2dva
    oveq2d
    @0
    vx
    cc
    @9
    @6
    @14
    @9
    @7
    @2
    cmul
    co
    @6
    @14
    @2
    @7
    @18
    @14
    cA
    @1
    @27
    @15
    cxpcld
    mulcomd
    @14
    @7
    @4
    @2
    cmul
    @28
    oveq1d
    eqtrd
    mpteq2dva
    3eqtr4d
end
