include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cfallfac.mm"
include "co.mm"
include "cc0.mm"
include "caddc.mm"
include "0p1e1.mm"
include "oveq2i.mm"
include "cmin.mm"
include "cmul.mm"
include "cn0.mm"
include "wceq.mm"
include "0nn0.mm"
include "fallfacp1.mm"
include "mpan2.mm"
include "fallfac0.mm"
include "subid1.mm"
include "oveq12d.mm"
include "mulid2.mm"
include "3eqtrd.mm"
include "syl5eqr.mm"

theorem fallfac1
  let cA: class A


  assert |- ( A e. CC -> ( A FallFac 1 ) = A )

  proof
    cA
    cc
    wcel
    #
    cA
    c1
    cfallfac
    co
    cA
    cc0
    c1
    caddc
    co
    #
    cfallfac
    co
    #
    cA
    @1
    c1
    cA
    cfallfac
    0p1e1
    oveq2i
    @0
    @2
    cA
    cc0
    cfallfac
    co
    #
    cA
    cc0
    cmin
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
    fallfacp1
    mpan2
    @0
    @3
    c1
    @4
    cA
    cmul
    cA
    fallfac0
    cA
    subid1
    oveq12d
    cA
    mulid2
    3eqtrd
    syl5eqr
end
