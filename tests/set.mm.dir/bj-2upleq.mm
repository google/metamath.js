include "wceq.mm"
include "bj-c1upl.mm"
include "c1o.mm"
include "csn.mm"
include "bj-ctag.mm"
include "cxp.mm"
include "cun.mm"
include "bj-c2uple.mm"
include "bj-1upleq.mm"
include "bj-xtageq.mm"
include "uneq12.mm"
include "ex.mm"
include "syl2im.mm"
include "df-bj-2upl.mm"
include "eqeq12i.mm"
include "syl6ibr.mm"

theorem bj-2upleq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A = B -> ( C = D -> (| A ,, C |) = (| B ,, D |) ) )

  proof
    cA
    cB
    wceq
    #
    cC
    cD
    wceq
    #
    cA
    bj-c1upl
    #
    c1o
    csn
    #
    cC
    bj-ctag
    cxp
    #
    cun
    #
    cB
    bj-c1upl
    #
    @3
    cD
    bj-ctag
    cxp
    #
    cun
    #
    wceq
    #
    cA
    cC
    bj-c2uple
    #
    cB
    cD
    bj-c2uple
    #
    wceq
    @0
    @2
    @6
    wceq
    #
    @1
    @4
    @7
    wceq
    #
    @9
    cA
    cB
    bj-1upleq
    cC
    cD
    @3
    bj-xtageq
    @12
    @13
    @9
    @2
    @6
    @4
    @7
    uneq12
    ex
    syl2im
    @10
    @5
    @11
    @8
    cA
    cC
    df-bj-2upl
    cB
    cD
    df-bj-2upl
    eqeq12i
    syl6ibr
end
