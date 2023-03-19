include "wne.mm"
include "wa.mm"
include "cpr.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "c0.mm"
include "ctp.mm"
include "cin.mm"
include "wceq.mm"
include "disjprsn.mm"
include "disj3.mm"
include "sylib.mm"
include "eqcomd.mm"
include "difid.mm"
include "a1i.mm"
include "uneq12d.mm"
include "df-tp.mm"
include "difeq1i.mm"
include "difundir.mm"
include "eqtr2i.mm"
include "un0.mm"
include "3eqtr3g.mm"

theorem diftpsn3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A =/= C /\ B =/= C ) -> ( { A , B , C } \ { C } ) = { A , B } )

  proof
    cA
    cC
    wne
    cB
    cC
    wne
    wa
    #
    cA
    cB
    cpr
    #
    cC
    csn
    #
    cdif
    #
    @2
    @2
    cdif
    #
    cun
    #
    @1
    c0
    cun
    cA
    cB
    cC
    ctp
    #
    @2
    cdif
    #
    @1
    @0
    @3
    @1
    @4
    c0
    @0
    @1
    @3
    @0
    @1
    @2
    cin
    c0
    wceq
    @1
    @3
    wceq
    cA
    cB
    cC
    disjprsn
    @1
    @2
    disj3
    sylib
    eqcomd
    @4
    c0
    wceq
    @0
    @2
    difid
    a1i
    uneq12d
    @7
    @1
    @2
    cun
    #
    @2
    cdif
    @5
    @6
    @8
    @2
    cA
    cB
    cC
    df-tp
    difeq1i
    @1
    @2
    @2
    difundir
    eqtr2i
    @1
    un0
    3eqtr3g
end
