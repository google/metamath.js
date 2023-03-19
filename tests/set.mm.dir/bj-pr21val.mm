include "bj-c2uple.mm"
include "bj-cpr1.mm"
include "bj-c1upl.mm"
include "c1o.mm"
include "csn.mm"
include "bj-ctag.mm"
include "cxp.mm"
include "cun.mm"
include "wceq.mm"
include "df-bj-2upl.mm"
include "bj-pr1eq.mm"
include "ax-mp.mm"
include "bj-pr1un.mm"
include "c0.mm"
include "bj-pr11val.mm"
include "cif.mm"
include "bj-pr1val.mm"
include "1n0.mm"
include "neii.mm"
include "iffalsei.mm"
include "eqtri.mm"
include "uneq12i.mm"
include "un0.mm"
include "3eqtri.mm"

theorem bj-pr21val
  let cA: class A
  let cB: class B


  assert |- pr1 (| A ,, B |) = A

  proof
    cA
    cB
    bj-c2uple
    #
    bj-cpr1
    #
    cA
    bj-c1upl
    #
    c1o
    csn
    cB
    bj-ctag
    cxp
    #
    cun
    #
    bj-cpr1
    #
    @2
    bj-cpr1
    #
    @3
    bj-cpr1
    #
    cun
    #
    cA
    @0
    @4
    wceq
    @1
    @5
    wceq
    cA
    cB
    df-bj-2upl
    @0
    @4
    bj-pr1eq
    ax-mp
    @2
    @3
    bj-pr1un
    @8
    cA
    c0
    cun
    cA
    @6
    cA
    @7
    c0
    cA
    bj-pr11val
    @7
    c1o
    c0
    wceq
    #
    cB
    c0
    cif
    c0
    c1o
    cB
    bj-pr1val
    @9
    cB
    c0
    c1o
    c0
    1n0
    neii
    iffalsei
    eqtri
    uneq12i
    cA
    un0
    eqtri
    3eqtri
end
