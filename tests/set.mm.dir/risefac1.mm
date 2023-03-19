include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "crisefac.mm"
include "co.mm"
include "cc0.mm"
include "caddc.mm"
include "0p1e1.mm"
include "oveq2i.mm"
include "cmul.mm"
include "cn0.mm"
include "wceq.mm"
include "0nn0.mm"
include "risefacp1.mm"
include "mpan2.mm"
include "risefac0.mm"
include "addid1.mm"
include "oveq12d.mm"
include "mulid2.mm"
include "3eqtrd.mm"
include "syl5eqr.mm"

theorem risefac1
  let cA: class A


  assert |- ( A e. CC -> ( A RiseFac 1 ) = A )

  proof
    cA
    cc
    wcel
    #
    cA
    c1
    crisefac
    co
    cA
    cc0
    c1
    caddc
    co
    #
    crisefac
    co
    #
    cA
    @1
    c1
    cA
    crisefac
    0p1e1
    oveq2i
    @0
    @2
    cA
    cc0
    crisefac
    co
    #
    cA
    cc0
    caddc
    co
    #
    cmul
    co
    #
    c1
    cA
    cmul
    co
    cA
    @0
    cc0
    cn0
    wcel
    @2
    @5
    wceq
    0nn0
    cA
    cc0
    risefacp1
    mpan2
    @0
    @3
    c1
    @4
    cA
    cmul
    cA
    risefac0
    cA
    addid1
    oveq12d
    cA
    mulid2
    3eqtrd
    syl5eqr
end
