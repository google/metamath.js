include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "ccxp.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "cif.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "ce.mm"
include "0cn.mm"
include "cxpval.mm"
include "mpan.mm"
include "eqid.mm"
include "iftruei.mm"
include "syl6eq.mm"
include "ifnefalse.mm"
include "sylan9eq.mm"

theorem 0cxp
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( 0 ^c A ) = 0 )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    cc0
    cA
    ccxp
    co
    #
    cA
    cc0
    wceq
    c1
    cc0
    cif
    #
    cc0
    @0
    @1
    cc0
    cc0
    wceq
    #
    @2
    cA
    cc0
    clog
    cfv
    cmul
    co
    ce
    cfv
    #
    cif
    #
    @2
    cc0
    cc
    wcel
    @0
    @1
    @5
    wceq
    0cn
    cc0
    cA
    cxpval
    mpan
    @3
    @2
    @4
    cc0
    eqid
    iftruei
    syl6eq
    cA
    cc0
    c1
    cc0
    ifnefalse
    sylan9eq
end
