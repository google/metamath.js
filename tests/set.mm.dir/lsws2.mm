include "wcel.mm"
include "cs2.mm"
include "clsw.mm"
include "cfv.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cvv.mm"
include "cword.mm"
include "wceq.mm"
include "s2cli.mm"
include "lsw.mm"
include "mp1i.mm"
include "c2.mm"
include "s2len.mm"
include "oveq1i.mm"
include "2m1e1.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "a1i.mm"
include "s2fv1.mm"
include "3eqtrd.mm"

theorem lsws2
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( B e. V -> ( lastS ` <" A B "> ) = B )

  proof
    cB
    cV
    wcel
    #
    cA
    cB
    cs2
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
    c1
    @1
    cfv
    #
    cB
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
    s2cli
    @1
    @7
    lsw
    mp1i
    @5
    @6
    wceq
    @0
    @4
    c1
    @1
    @4
    c2
    c1
    cmin
    co
    c1
    @3
    c2
    c1
    cmin
    cA
    cB
    s2len
    oveq1i
    2m1e1
    eqtri
    fveq2i
    a1i
    cA
    cB
    cV
    s2fv1
    3eqtrd
end
