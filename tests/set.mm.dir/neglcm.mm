include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "clcm.mm"
include "co.mm"
include "wceq.mm"
include "lcmneg.mm"
include "ancoms.mm"
include "znegcl.mm"
include "lcmcom.mm"
include "sylan.mm"
include "3eqtr4d.mm"

theorem neglcm
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( -u M lcm N ) = ( M lcm N ) )

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
    cN
    cM
    cneg
    #
    clcm
    co
    #
    cN
    cM
    clcm
    co
    #
    @2
    cN
    clcm
    co
    #
    cM
    cN
    clcm
    co
    @1
    @0
    @3
    @4
    wceq
    cN
    cM
    lcmneg
    ancoms
    @0
    @2
    cz
    wcel
    @1
    @5
    @3
    wceq
    cM
    znegcl
    @2
    cN
    lcmcom
    sylan
    cM
    cN
    lcmcom
    3eqtr4d
end
