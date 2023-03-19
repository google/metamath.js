include "csn.mm"
include "bj-ctag.mm"
include "cxp.mm"
include "bj-cpr2.mm"
include "c1o.mm"
include "bj-cproj.mm"
include "wceq.mm"
include "c0.mm"
include "cif.mm"
include "df-bj-pr2.mm"
include "cvv.mm"
include "wcel.mm"
include "bj-1ex.mm"
include "bj-projval.mm"
include "ax-mp.mm"
include "eqtri.mm"

theorem bj-pr2val
  let cA: class A
  let cB: class B


  assert |- pr2 ( { A } X. tag B ) = if ( A = 1o , B , (/) )

  proof
    cA
    csn
    cB
    bj-ctag
    cxp
    #
    bj-cpr2
    c1o
    @0
    bj-cproj
    #
    cA
    c1o
    wceq
    cB
    c0
    cif
    #
    @0
    df-bj-pr2
    c1o
    cvv
    wcel
    @1
    @2
    wceq
    bj-1ex
    c1o
    cA
    cB
    cvv
    bj-projval
    ax-mp
    eqtri
end
