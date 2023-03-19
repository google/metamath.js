include "csn.mm"
include "bj-ctag.mm"
include "cxp.mm"
include "bj-cpr1.mm"
include "c0.mm"
include "bj-cproj.mm"
include "wceq.mm"
include "cif.mm"
include "df-bj-pr1.mm"
include "cvv.mm"
include "wcel.mm"
include "0ex.mm"
include "bj-projval.mm"
include "ax-mp.mm"
include "eqtri.mm"

theorem bj-pr1val
  let cA: class A
  let cB: class B


  assert |- pr1 ( { A } X. tag B ) = if ( A = (/) , B , (/) )

  proof
    cA
    csn
    cB
    bj-ctag
    cxp
    #
    bj-cpr1
    c0
    @0
    bj-cproj
    #
    cA
    c0
    wceq
    cB
    c0
    cif
    #
    @0
    df-bj-pr1
    c0
    cvv
    wcel
    @1
    @2
    wceq
    0ex
    c0
    cA
    cB
    cvv
    bj-projval
    ax-mp
    eqtri
end
