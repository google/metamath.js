include "cdif.mm"
include "wceq.mm"
include "cin.mm"
include "c0.mm"
include "cun.mm"
include "wa.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtr3i.mm"
include "ineq1.mm"
include "syl5reqr.mm"
include "undif1.mm"
include "uneq1.mm"
include "jca.mm"
include "simpl.mm"
include "disj3.mm"
include "eqcom.mm"
include "bitri.mm"
include "sylib.mm"
include "wb.mm"
include "difeq1.mm"
include "difun2.mm"
include "3eqtr3g.mm"
include "eqeq1d.mm"
include "adantl.mm"
include "mpbid.mm"
include "impbii.mm"

theorem difeq
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A \ B ) = C <-> ( ( C i^i B ) = (/) /\ ( C u. B ) = ( A u. B ) ) )

  proof
    cA
    cB
    cdif
    #
    cC
    wceq
    #
    cC
    cB
    cin
    #
    c0
    wceq
    #
    cC
    cB
    cun
    #
    cA
    cB
    cun
    #
    wceq
    #
    wa
    #
    @1
    @3
    @6
    @1
    c0
    @0
    cB
    cin
    #
    @2
    cB
    @0
    cin
    @8
    c0
    cB
    @0
    incom
    cB
    cA
    disjdif
    eqtr3i
    @0
    cC
    cB
    ineq1
    syl5reqr
    @1
    @5
    @0
    cB
    cun
    @4
    cA
    cB
    undif1
    @0
    cC
    cB
    uneq1
    syl5reqr
    jca
    @7
    cC
    cB
    cdif
    #
    cC
    wceq
    #
    @1
    @7
    @3
    @10
    @3
    @6
    simpl
    @3
    cC
    @9
    wceq
    @10
    cC
    cB
    disj3
    cC
    @9
    eqcom
    bitri
    sylib
    @6
    @10
    @1
    wb
    @3
    @6
    @9
    @0
    cC
    @6
    @4
    cB
    cdif
    @5
    cB
    cdif
    @9
    @0
    @4
    @5
    cB
    difeq1
    cC
    cB
    difun2
    cA
    cB
    difun2
    3eqtr3g
    eqeq1d
    adantl
    mpbid
    impbii
end
