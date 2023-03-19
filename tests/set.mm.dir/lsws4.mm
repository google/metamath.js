include "wcel.mm"
include "cs4.mm"
include "clsw.mm"
include "cfv.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c3.mm"
include "cvv.mm"
include "cword.mm"
include "wceq.mm"
include "s4cli.mm"
include "lsw.mm"
include "mp1i.mm"
include "c4.mm"
include "s4len.mm"
include "oveq1i.mm"
include "4m1e3.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "a1i.mm"
include "s4fv3.mm"
include "3eqtrd.mm"

theorem lsws4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V


  assert |- ( D e. V -> ( lastS ` <" A B C D "> ) = D )

  proof
    cD
    cV
    wcel
    #
    cA
    cB
    cC
    cD
    cs4
    #
    clsw
    cfv
    #
    @1
    chash
    cfv
    #
    c1
    cmin
    co
    #
    @1
    cfv
    #
    c3
    @1
    cfv
    #
    cD
    @1
    cvv
    cword
    #
    wcel
    @2
    @5
    wceq
    @0
    cA
    cB
    cC
    cD
    s4cli
    @1
    @7
    lsw
    mp1i
    @5
    @6
    wceq
    @0
    @4
    c3
    @1
    @4
    c4
    c1
    cmin
    co
    c3
    @3
    c4
    c1
    cmin
    cA
    cB
    cC
    cD
    s4len
    oveq1i
    4m1e3
    eqtri
    fveq2i
    a1i
    cA
    cB
    cC
    cD
    cV
    s4fv3
    3eqtrd
end
