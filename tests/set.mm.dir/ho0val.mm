include "chil.mm"
include "wcel.mm"
include "ch0o.mm"
include "cfv.mm"
include "cpjh.mm"
include "cmv.mm"
include "co.mm"
include "c0v.mm"
include "cort.mm"
include "c0h.mm"
include "choc1.mm"
include "fveq2i.mm"
include "df-h0op.mm"
include "eqtr4i.mm"
include "fveq1i.mm"
include "cch.mm"
include "wceq.mm"
include "helch.mm"
include "pjo.mm"
include "mpan.mm"
include "syl5eqr.mm"
include "pjhcli.mm"
include "hvsubid.mm"
include "syl.mm"
include "eqtrd.mm"

theorem ho0val
  let cA: class A


  assert |- ( A e. ~H -> ( 0hop ` A ) = 0h )

  proof
    cA
    chil
    wcel
    #
    cA
    ch0o
    cfv
    #
    cA
    chil
    cpjh
    cfv
    cfv
    #
    @2
    cmv
    co
    #
    c0v
    @0
    @1
    cA
    chil
    cort
    cfv
    #
    cpjh
    cfv
    #
    cfv
    #
    @3
    cA
    @5
    ch0o
    @5
    c0h
    cpjh
    cfv
    ch0o
    @4
    c0h
    cpjh
    choc1
    fveq2i
    df-h0op
    eqtr4i
    fveq1i
    chil
    cch
    wcel
    @0
    @6
    @3
    wceq
    helch
    cA
    chil
    pjo
    mpan
    syl5eqr
    @0
    @2
    chil
    wcel
    @3
    c0v
    wceq
    cA
    chil
    helch
    pjhcli
    @2
    hvsubid
    syl
    eqtrd
end
