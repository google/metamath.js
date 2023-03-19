include "wne.mm"
include "wa.mm"
include "ctp.mm"
include "csn.mm"
include "cdif.mm"
include "cpr.mm"
include "cun.mm"
include "wceq.mm"
include "df-tp.mm"
include "a1i.mm"
include "difeq1d.mm"
include "difundir.mm"
include "c0.mm"
include "cin.mm"
include "df-pr.mm"
include "ineq1d.mm"
include "incom.mm"
include "indi.mm"
include "eqtri.mm"
include "necom.mm"
include "disjsn2.mm"
include "sylbi.mm"
include "adantr.mm"
include "adantl.mm"
include "uneq12d.mm"
include "unidm.mm"
include "syl6eq.mm"
include "3eqtrd.mm"
include "disj3.mm"
include "sylib.mm"
include "eqcomd.mm"
include "difid.mm"
include "un0.mm"

theorem diftpsn3OLD
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A =/= C /\ B =/= C ) -> ( { A , B , C } \ { C } ) = { A , B } )

  proof
    cA
    cC
    wne
    #
    cB
    cC
    wne
    #
    wa
    #
    cA
    cB
    cC
    ctp
    #
    cC
    csn
    #
    cdif
    cA
    cB
    cpr
    #
    @4
    cun
    #
    @4
    cdif
    #
    @5
    @4
    cdif
    #
    @4
    @4
    cdif
    #
    cun
    #
    @5
    @2
    @3
    @6
    @4
    @3
    @6
    wceq
    @2
    cA
    cB
    cC
    df-tp
    a1i
    difeq1d
    @7
    @10
    wceq
    @2
    @5
    @4
    @4
    difundir
    a1i
    @2
    @10
    @5
    c0
    cun
    @5
    @2
    @8
    @5
    @9
    c0
    @2
    @5
    @8
    @2
    @5
    @4
    cin
    #
    c0
    wceq
    @5
    @8
    wceq
    @2
    @11
    cA
    csn
    #
    cB
    csn
    #
    cun
    #
    @4
    cin
    #
    @4
    @12
    cin
    #
    @4
    @13
    cin
    #
    cun
    #
    c0
    @2
    @5
    @14
    @4
    @5
    @14
    wceq
    @2
    cA
    cB
    df-pr
    a1i
    ineq1d
    @15
    @18
    wceq
    @2
    @15
    @4
    @14
    cin
    @18
    @14
    @4
    incom
    @4
    @12
    @13
    indi
    eqtri
    a1i
    @2
    @18
    c0
    c0
    cun
    c0
    @2
    @16
    c0
    @17
    c0
    @0
    @16
    c0
    wceq
    #
    @1
    @0
    cC
    cA
    wne
    @19
    cA
    cC
    necom
    cC
    cA
    disjsn2
    sylbi
    adantr
    @1
    @17
    c0
    wceq
    #
    @0
    @1
    cC
    cB
    wne
    @20
    cB
    cC
    necom
    cC
    cB
    disjsn2
    sylbi
    adantl
    uneq12d
    c0
    unidm
    syl6eq
    3eqtrd
    @5
    @4
    disj3
    sylib
    eqcomd
    @9
    c0
    wceq
    @2
    @4
    difid
    a1i
    uneq12d
    @5
    un0
    syl6eq
    3eqtrd
end
