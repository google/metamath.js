include "bj-c2uple.mm"
include "bj-cpr2.mm"
include "bj-c1upl.mm"
include "c1o.mm"
include "csn.mm"
include "bj-ctag.mm"
include "cxp.mm"
include "cun.mm"
include "c0.mm"
include "wceq.mm"
include "df-bj-2upl.mm"
include "bj-pr2eq.mm"
include "ax-mp.mm"
include "bj-pr2un.mm"
include "eqtri.mm"
include "cif.mm"
include "df-bj-1upl.mm"
include "bj-pr2val.mm"
include "1n0.mm"
include "nesymi.mm"
include "iffalsei.mm"
include "3eqtri.mm"
include "eqid.mm"
include "iftruei.mm"
include "uneq12i.mm"
include "uncom.mm"
include "un0.mm"

theorem bj-pr22val
  let cA: class A
  let cB: class B


  assert |- pr2 (| A ,, B |) = B

  proof
    cA
    cB
    bj-c2uple
    #
    bj-cpr2
    #
    cA
    bj-c1upl
    #
    bj-cpr2
    #
    c1o
    csn
    cB
    bj-ctag
    cxp
    #
    bj-cpr2
    #
    cun
    #
    c0
    cB
    cun
    #
    cB
    @1
    @2
    @4
    cun
    #
    bj-cpr2
    #
    @6
    @0
    @8
    wceq
    @1
    @9
    wceq
    cA
    cB
    df-bj-2upl
    @0
    @8
    bj-pr2eq
    ax-mp
    @2
    @4
    bj-pr2un
    eqtri
    @3
    c0
    @5
    cB
    @3
    c0
    csn
    cA
    bj-ctag
    cxp
    #
    bj-cpr2
    #
    c0
    c1o
    wceq
    #
    cA
    c0
    cif
    c0
    @2
    @10
    wceq
    @3
    @11
    wceq
    cA
    df-bj-1upl
    @2
    @10
    bj-pr2eq
    ax-mp
    c0
    cA
    bj-pr2val
    @12
    cA
    c0
    c1o
    c0
    1n0
    nesymi
    iffalsei
    3eqtri
    @5
    c1o
    c1o
    wceq
    #
    cB
    c0
    cif
    cB
    c1o
    cB
    bj-pr2val
    @13
    cB
    c0
    c1o
    eqid
    iftruei
    eqtri
    uneq12i
    @7
    cB
    c0
    cun
    cB
    c0
    cB
    uncom
    cB
    un0
    eqtri
    3eqtri
end
