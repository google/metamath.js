include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "cneg.mm"
include "wo.mm"
include "clcm.mm"
include "co.mm"
include "cr.mm"
include "zre.mm"
include "absor.mm"
include "anim12i.mm"
include "syl2an.mm"
include "wi.mm"
include "oveq12.mm"
include "a1i.mm"
include "neglcm.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "lcmneg.mm"
include "znegcl.mm"
include "sylan.mm"
include "eqtrd.mm"
include "ccased.mm"
include "mpd.mm"

theorem lcmabs
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( ( abs ` M ) lcm ( abs ` N ) ) = ( M lcm N ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cM
    cabs
    cfv
    #
    cM
    wceq
    #
    @3
    cM
    cneg
    #
    wceq
    #
    wo
    #
    cN
    cabs
    cfv
    #
    cN
    wceq
    #
    @8
    cN
    cneg
    #
    wceq
    #
    wo
    #
    wa
    #
    @3
    @8
    clcm
    co
    #
    cM
    cN
    clcm
    co
    #
    wceq
    #
    @0
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @13
    @1
    cM
    zre
    cN
    zre
    @17
    @7
    @18
    @12
    cM
    absor
    cN
    absor
    anim12i
    syl2an
    @2
    @4
    @9
    @6
    @11
    @16
    @4
    @9
    wa
    @16
    wi
    @2
    @3
    cM
    @8
    cN
    clcm
    oveq12
    a1i
    @2
    @6
    @9
    wa
    #
    @16
    @19
    @2
    @14
    @5
    cN
    clcm
    co
    #
    @15
    @3
    @5
    @8
    cN
    clcm
    oveq12
    cM
    cN
    neglcm
    #
    sylan9eqr
    ex
    @2
    @4
    @11
    wa
    #
    @16
    @22
    @2
    @14
    cM
    @10
    clcm
    co
    @15
    @3
    cM
    @8
    @10
    clcm
    oveq12
    cM
    cN
    lcmneg
    sylan9eqr
    ex
    @2
    @6
    @11
    wa
    #
    @16
    @23
    @2
    @14
    @5
    @10
    clcm
    co
    #
    @15
    @3
    @5
    @8
    @10
    clcm
    oveq12
    @2
    @24
    @20
    @15
    @0
    @5
    cz
    wcel
    @1
    @24
    @20
    wceq
    cM
    znegcl
    @5
    cN
    lcmneg
    sylan
    @21
    eqtrd
    sylan9eqr
    ex
    ccased
    mpd
end
