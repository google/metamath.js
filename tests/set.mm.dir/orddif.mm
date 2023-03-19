include "word.mm"
include "csn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "csuc.mm"
include "cdif.mm"
include "orddisj.mm"
include "disj3.mm"
include "cun.mm"
include "df-suc.mm"
include "difeq1i.mm"
include "difun2.mm"
include "eqtri.mm"
include "eqeq2i.mm"
include "bitr4i.mm"
include "sylib.mm"

theorem orddif
  let cA: class A


  assert |- ( Ord A -> A = ( suc A \ { A } ) )

  proof
    cA
    word
    cA
    cA
    csn
    #
    cin
    c0
    wceq
    #
    cA
    cA
    csuc
    #
    @0
    cdif
    #
    wceq
    #
    cA
    orddisj
    @1
    cA
    cA
    @0
    cdif
    #
    wceq
    @4
    cA
    @0
    disj3
    @3
    @5
    cA
    @3
    cA
    @0
    cun
    #
    @0
    cdif
    @5
    @2
    @6
    @0
    cA
    df-suc
    difeq1i
    cA
    @0
    difun2
    eqtri
    eqeq2i
    bitr4i
    sylib
end
