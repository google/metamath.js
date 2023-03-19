include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "clcm.mm"
include "co.mm"
include "cgcd.mm"
include "cmul.mm"
include "cabs.mm"
include "cfv.mm"
include "gcd1.mm"
include "oveq2d.mm"
include "cn0.mm"
include "1z.mm"
include "lcmcl.mm"
include "mpan2.mm"
include "nn0cnd.mm"
include "mulid1d.mm"
include "eqtr2d.mm"
include "wceq.mm"
include "lcmgcd.mm"
include "zcn.mm"
include "fveq2d.mm"
include "3eqtrd.mm"

theorem lcm1
  let cM: class M


  assert |- ( M e. ZZ -> ( M lcm 1 ) = ( abs ` M ) )

  proof
    cM
    cz
    wcel
    #
    cM
    c1
    clcm
    co
    #
    @1
    cM
    c1
    cgcd
    co
    #
    cmul
    co
    #
    cM
    c1
    cmul
    co
    #
    cabs
    cfv
    #
    cM
    cabs
    cfv
    @0
    @3
    @1
    c1
    cmul
    co
    @1
    @0
    @2
    c1
    @1
    cmul
    cM
    gcd1
    oveq2d
    @0
    @1
    @0
    @1
    @0
    c1
    cz
    wcel
    #
    @1
    cn0
    wcel
    1z
    cM
    c1
    lcmcl
    mpan2
    nn0cnd
    mulid1d
    eqtr2d
    @0
    @6
    @3
    @5
    wceq
    1z
    cM
    c1
    lcmgcd
    mpan2
    @0
    @4
    cM
    cabs
    @0
    cM
    cM
    zcn
    mulid1d
    fveq2d
    3eqtrd
end
