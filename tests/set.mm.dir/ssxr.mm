include "cr.mm"
include "cpnf.mm"
include "cmnf.mm"
include "cpr.mm"
include "cun.mm"
include "wss.mm"
include "wcel.mm"
include "wo.mm"
include "cxr.mm"
include "w3o.mm"
include "wn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "csn.mm"
include "df-pr.mm"
include "ineq2i.mm"
include "indi.mm"
include "eqtri.mm"
include "wa.mm"
include "disjsn.mm"
include "anbi12i.mm"
include "biimpri.mm"
include "pm4.56.mm"
include "un00.mm"
include "3imtr3i.mm"
include "syl5eq.mm"
include "cdif.mm"
include "reldisj.mm"
include "renfdisj.mm"
include "disj3.mm"
include "mpbi.mm"
include "difun2.mm"
include "eqtr4i.mm"
include "sseq2i.mm"
include "syl6bbr.mm"
include "syl5ib.mm"
include "orrd.mm"
include "df-xr.mm"
include "3orrot.mm"
include "df-3or.mm"
include "bitri.mm"
include "3imtr4i.mm"

theorem ssxr
  let cA: class A


  assert |- ( A C_ RR* -> ( A C_ RR \/ +oo e. A \/ -oo e. A ) )

  proof
    cA
    cr
    cpnf
    cmnf
    cpr
    #
    cun
    #
    wss
    #
    cpnf
    cA
    wcel
    #
    cmnf
    cA
    wcel
    #
    wo
    #
    cA
    cr
    wss
    #
    wo
    #
    cA
    cxr
    wss
    @6
    @3
    @4
    w3o
    #
    @2
    @5
    @6
    @5
    wn
    #
    cA
    @0
    cin
    #
    c0
    wceq
    #
    @2
    @6
    @9
    @10
    cA
    cpnf
    csn
    #
    cin
    #
    cA
    cmnf
    csn
    #
    cin
    #
    cun
    #
    c0
    @10
    cA
    @12
    @14
    cun
    #
    cin
    @16
    @0
    @17
    cA
    cpnf
    cmnf
    df-pr
    ineq2i
    cA
    @12
    @14
    indi
    eqtri
    @3
    wn
    #
    @4
    wn
    #
    wa
    #
    @13
    c0
    wceq
    #
    @15
    c0
    wceq
    #
    wa
    #
    @9
    @16
    c0
    wceq
    @23
    @20
    @21
    @18
    @22
    @19
    cA
    cpnf
    disjsn
    cA
    cmnf
    disjsn
    anbi12i
    biimpri
    @3
    @4
    pm4.56
    @13
    @15
    un00
    3imtr3i
    syl5eq
    @2
    @11
    cA
    @1
    @0
    cdif
    #
    wss
    @6
    cA
    @0
    @1
    reldisj
    cr
    @24
    cA
    cr
    cr
    @0
    cdif
    #
    @24
    cr
    @0
    cin
    c0
    wceq
    cr
    @25
    wceq
    renfdisj
    cr
    @0
    disj3
    mpbi
    cr
    @0
    difun2
    eqtr4i
    sseq2i
    syl6bbr
    syl5ib
    orrd
    cxr
    @1
    cA
    df-xr
    sseq2i
    @8
    @3
    @4
    @6
    w3o
    @7
    @6
    @3
    @4
    3orrot
    @3
    @4
    @6
    df-3or
    bitri
    3imtr4i
end
