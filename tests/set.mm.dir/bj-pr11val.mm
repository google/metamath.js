include "bj-c1upl.mm"
include "bj-cpr1.mm"
include "c0.mm"
include "csn.mm"
include "bj-ctag.mm"
include "cxp.mm"
include "wceq.mm"
include "cif.mm"
include "df-bj-1upl.mm"
include "bj-pr1eq.mm"
include "ax-mp.mm"
include "bj-pr1val.mm"
include "eqid.mm"
include "iftruei.mm"
include "3eqtri.mm"

theorem bj-pr11val
  let cA: class A


  assert |- pr1 (| A |) = A

  proof
    cA
    bj-c1upl
    #
    bj-cpr1
    #
    c0
    csn
    cA
    bj-ctag
    cxp
    #
    bj-cpr1
    #
    c0
    c0
    wceq
    #
    cA
    c0
    cif
    cA
    @0
    @2
    wceq
    @1
    @3
    wceq
    cA
    df-bj-1upl
    @0
    @2
    bj-pr1eq
    ax-mp
    c0
    cA
    bj-pr1val
    @4
    cA
    c0
    c0
    eqid
    iftruei
    3eqtri
end
