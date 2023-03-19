include "cz.mm"
include "wcel.mm"
include "clcm.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "oveq2.mm"
include "fveq2.mm"
include "abs0.mm"
include "syl6eq.mm"
include "eqeq12d.mm"
include "wne.mm"
include "wa.mm"
include "cc.mm"
include "lcmcl.mm"
include "nn0cnd.mm"
include "anidms.mm"
include "adantr.mm"
include "zabscl.mm"
include "zcnd.mm"
include "zcn.mm"
include "simpr.mm"
include "absne0d.mm"
include "cmul.mm"
include "cgcd.mm"
include "lcmgcd.mm"
include "gcdid.mm"
include "oveq2d.mm"
include "absmuld.mm"
include "3eqtr3d.mm"
include "mulcan2ad.mm"
include "lcm0val.mm"
include "pm2.61ne.mm"

theorem lcmid
  let cM: class M


  assert |- ( M e. ZZ -> ( M lcm M ) = ( abs ` M ) )

  proof
    cM
    cz
    wcel
    #
    cM
    cM
    clcm
    co
    #
    cM
    cabs
    cfv
    #
    wceq
    cM
    cc0
    clcm
    co
    #
    cc0
    wceq
    cM
    cc0
    cM
    cc0
    wceq
    #
    @1
    @3
    @2
    cc0
    cM
    cc0
    cM
    clcm
    oveq2
    @4
    @2
    cc0
    cabs
    cfv
    cc0
    cM
    cc0
    cabs
    fveq2
    abs0
    syl6eq
    eqeq12d
    @0
    cM
    cc0
    wne
    #
    wa
    #
    @1
    @2
    @2
    @0
    @1
    cc
    wcel
    #
    @5
    @0
    @7
    @0
    @0
    wa
    @1
    cM
    cM
    lcmcl
    nn0cnd
    anidms
    adantr
    @0
    @2
    cc
    wcel
    @5
    @0
    @2
    cM
    zabscl
    zcnd
    adantr
    #
    @8
    @6
    cM
    @0
    cM
    cc
    wcel
    @5
    cM
    zcn
    #
    adantr
    @0
    @5
    simpr
    absne0d
    @0
    @1
    @2
    cmul
    co
    #
    @2
    @2
    cmul
    co
    #
    wceq
    @5
    @0
    @1
    cM
    cM
    cgcd
    co
    #
    cmul
    co
    #
    cM
    cM
    cmul
    co
    cabs
    cfv
    #
    @10
    @11
    @0
    @13
    @14
    wceq
    cM
    cM
    lcmgcd
    anidms
    @0
    @12
    @2
    @1
    cmul
    cM
    gcdid
    oveq2d
    @0
    cM
    cM
    @9
    @9
    absmuld
    3eqtr3d
    adantr
    mulcan2ad
    cM
    lcm0val
    pm2.61ne
end
