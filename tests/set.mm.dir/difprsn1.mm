include "wne.mm"
include "cpr.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "necom.mm"
include "cin.mm"
include "c0.mm"
include "disjsn2.mm"
include "disj3.mm"
include "sylib.mm"
include "cun.mm"
include "df-pr.mm"
include "equncomi.mm"
include "difeq1i.mm"
include "difun2.mm"
include "eqtri.mm"
include "syl6reqr.mm"
include "sylbir.mm"

theorem difprsn1
  let cA: class A
  let cB: class B


  assert |- ( A =/= B -> ( { A , B } \ { A } ) = { B } )

  proof
    cA
    cB
    wne
    cB
    cA
    wne
    #
    cA
    cB
    cpr
    #
    cA
    csn
    #
    cdif
    #
    cB
    csn
    #
    wceq
    cB
    cA
    necom
    @0
    @4
    @4
    @2
    cdif
    #
    @3
    @0
    @4
    @2
    cin
    c0
    wceq
    @4
    @5
    wceq
    cB
    cA
    disjsn2
    @4
    @2
    disj3
    sylib
    @3
    @4
    @2
    cun
    #
    @2
    cdif
    @5
    @1
    @6
    @2
    @1
    @2
    @4
    cA
    cB
    df-pr
    equncomi
    difeq1i
    @4
    @2
    difun2
    eqtri
    syl6reqr
    sylbir
end
