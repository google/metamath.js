include "wcel.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wsbc.mm"
include "csb.mm"
include "wrel.mm"
include "sbcssg.mm"
include "csbconstg.mm"
include "sseq2d.mm"
include "bitrd.mm"
include "df-rel.mm"
include "sbcbii.mm"
include "3bitr4g.mm"

theorem sbcrel
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cV: class V


  assert |- ( A e. V -> ( [. A / x ]. Rel R <-> Rel [_ A / x ]_ R ) )

  proof
    cA
    cV
    wcel
    #
    cR
    cvv
    cvv
    cxp
    #
    wss
    #
    vx
    cA
    wsbc
    #
    vx
    cA
    cR
    csb
    #
    @1
    wss
    #
    cR
    wrel
    #
    vx
    cA
    wsbc
    @4
    wrel
    @0
    @3
    @4
    vx
    cA
    @1
    csb
    #
    wss
    @5
    vx
    cA
    cR
    @1
    cV
    sbcssg
    @0
    @7
    @1
    @4
    vx
    cA
    @1
    cV
    csbconstg
    sseq2d
    bitrd
    @6
    @2
    vx
    cA
    cR
    df-rel
    sbcbii
    @4
    df-rel
    3bitr4g
end
