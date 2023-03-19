include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cfallfac.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "cexp.mm"
include "crisefac.mm"
include "cmul.mm"
include "cn0.mm"
include "wceq.mm"
include "0nn0.mm"
include "fallrisefac.mm"
include "mpan2.mm"
include "neg1cn.mm"
include "exp0.mm"
include "mp1i.mm"
include "negcl.mm"
include "risefac0.mm"
include "syl.mm"
include "oveq12d.mm"
include "1t1e1.mm"
include "syl6eq.mm"
include "eqtrd.mm"

theorem fallfac0
  let cA: class A


  assert |- ( A e. CC -> ( A FallFac 0 ) = 1 )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    cfallfac
    co
    #
    c1
    cneg
    #
    cc0
    cexp
    co
    #
    cA
    cneg
    #
    cc0
    crisefac
    co
    #
    cmul
    co
    #
    c1
    @0
    cc0
    cn0
    wcel
    @1
    @6
    wceq
    0nn0
    cc0
    cA
    fallrisefac
    mpan2
    @0
    @6
    c1
    c1
    cmul
    co
    c1
    @0
    @3
    c1
    @5
    c1
    cmul
    @2
    cc
    wcel
    @3
    c1
    wceq
    @0
    neg1cn
    @2
    exp0
    mp1i
    @0
    @4
    cc
    wcel
    @5
    c1
    wceq
    cA
    negcl
    @4
    risefac0
    syl
    oveq12d
    1t1e1
    syl6eq
    eqtrd
end
