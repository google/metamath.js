include "com.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cdif.mm"
include "cun.mm"
include "csuc.mm"
include "word.mm"
include "nnord.mm"
include "wne.mm"
include "nordeq.mm"
include "disjsn2.mm"
include "syl.mm"
include "sylan.mm"
include "undif4.mm"
include "df-suc.mm"
include "equncomi.mm"
include "difeq1i.mm"
include "syl6eqr.mm"

theorem phplem1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. _om /\ B e. A ) -> ( { A } u. ( A \ { B } ) ) = ( suc A \ { B } ) )

  proof
    cA
    com
    wcel
    #
    cB
    cA
    wcel
    #
    wa
    cA
    csn
    #
    cB
    csn
    #
    cin
    c0
    wceq
    #
    @2
    cA
    @3
    cdif
    cun
    #
    cA
    csuc
    #
    @3
    cdif
    #
    wceq
    @0
    cA
    word
    #
    @1
    @4
    cA
    nnord
    @8
    @1
    wa
    cA
    cB
    wne
    @4
    cA
    cB
    nordeq
    cA
    cB
    disjsn2
    syl
    sylan
    @4
    @5
    @2
    cA
    cun
    #
    @3
    cdif
    @7
    @2
    cA
    @3
    undif4
    @6
    @9
    @3
    @6
    cA
    @2
    cA
    df-suc
    equncomi
    difeq1i
    syl6eqr
    syl
end
