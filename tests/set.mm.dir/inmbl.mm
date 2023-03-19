include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "cdif.mm"
include "cun.mm"
include "cin.mm"
include "difundi.mm"
include "wss.mm"
include "wceq.mm"
include "mblss.mm"
include "dfss4.mm"
include "sylib.mm"
include "ineqan12d.mm"
include "syl5eq.mm"
include "cmmbl.mm"
include "unmbl.mm"
include "syl2an.mm"
include "syl.mm"
include "eqeltrrd.mm"

theorem inmbl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom vol /\ B e. dom vol ) -> ( A i^i B ) e. dom vol )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cr
    cr
    cA
    cdif
    #
    cr
    cB
    cdif
    #
    cun
    #
    cdif
    #
    cA
    cB
    cin
    #
    @0
    @3
    @7
    cr
    @4
    cdif
    #
    cr
    @5
    cdif
    #
    cin
    @8
    cr
    @4
    @5
    difundi
    @1
    @2
    @9
    cA
    @10
    cB
    @1
    cA
    cr
    wss
    @9
    cA
    wceq
    cA
    mblss
    cA
    cr
    dfss4
    sylib
    @2
    cB
    cr
    wss
    @10
    cB
    wceq
    cB
    mblss
    cB
    cr
    dfss4
    sylib
    ineqan12d
    syl5eq
    @3
    @6
    @0
    wcel
    #
    @7
    @0
    wcel
    @1
    @4
    @0
    wcel
    @5
    @0
    wcel
    @11
    @2
    cA
    cmmbl
    cB
    cmmbl
    @4
    @5
    unmbl
    syl2an
    @6
    cmmbl
    syl
    eqeltrrd
end
