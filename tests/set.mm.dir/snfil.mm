include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "csn.mm"
include "wss.mm"
include "wb.mm"
include "velsn.mm"
include "eqimss.mm"
include "pm4.71ri.mm"
include "bitri.mm"
include "a1i.mm"
include "cvv.mm"
include "elex.mm"
include "adantr.mm"
include "wsbc.mm"
include "eqid.mm"
include "eqsbc3.mm"
include "mpbiri.mm"
include "simpr.mm"
include "necomd.mm"
include "neneqd.mm"
include "0ex.mm"
include "ax-mp.mm"
include "sylnibr.mm"
include "w3a.mm"
include "wi.mm"
include "sseq1.mm"
include "anbi2d.mm"
include "eqss.mm"
include "biimpri.mm"
include "syl6bi.mm"
include "com12.mm"
include "3adant1.mm"
include "sbcid.mm"
include "vex.mm"
include "3imtr4g.mm"
include "cin.mm"
include "ineq12.mm"
include "inidm.mm"
include "syl6eq.mm"
include "syl2anb.mm"
include "inex1.mm"
include "sylibr.mm"
include "isfild.mm"

theorem snfil
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. B /\ A =/= (/) ) -> { A } e. ( Fil ` A ) )

  proof
    cA
    cB
    wcel
    #
    cA
    c0
    wne
    #
    wa
    #
    vx
    cv
    #
    cA
    wceq
    #
    vx
    vy
    vx
    cA
    cA
    csn
    #
    @3
    @5
    wcel
    #
    @3
    cA
    wss
    #
    @4
    wa
    #
    wb
    @2
    @6
    @4
    @8
    vx
    cA
    velsn
    @4
    @7
    @3
    cA
    eqimss
    pm4.71ri
    bitri
    a1i
    @0
    cA
    cvv
    wcel
    @1
    cA
    cB
    elex
    adantr
    @0
    @4
    vx
    cA
    wsbc
    #
    @1
    @0
    @9
    cA
    cA
    wceq
    cA
    eqid
    vx
    cA
    cA
    cB
    eqsbc3
    mpbiri
    adantr
    @2
    c0
    cA
    wceq
    #
    @4
    vx
    c0
    wsbc
    #
    @2
    c0
    cA
    @2
    cA
    c0
    @0
    @1
    simpr
    necomd
    neneqd
    c0
    cvv
    wcel
    @11
    @10
    wb
    0ex
    vx
    c0
    cA
    cvv
    eqsbc3
    ax-mp
    sylnibr
    @2
    vy
    cv
    #
    cA
    wss
    #
    @3
    @12
    wss
    #
    w3a
    @4
    @12
    cA
    wceq
    #
    @4
    vx
    @3
    wsbc
    #
    @4
    vx
    @12
    wsbc
    #
    @13
    @14
    @4
    @15
    wi
    @2
    @4
    @13
    @14
    wa
    #
    @15
    @4
    @18
    @13
    cA
    @12
    wss
    #
    wa
    #
    @15
    @4
    @14
    @19
    @13
    @3
    cA
    @12
    sseq1
    anbi2d
    @15
    @20
    @12
    cA
    eqss
    biimpri
    syl6bi
    com12
    3adant1
    @4
    vx
    sbcid
    #
    @12
    cvv
    wcel
    @17
    @15
    wb
    vy
    vex
    #
    vx
    @12
    cA
    cvv
    eqsbc3
    ax-mp
    #
    3imtr4g
    @17
    @16
    wa
    #
    @4
    vx
    @12
    @3
    cin
    #
    wsbc
    #
    wi
    @2
    @13
    @7
    w3a
    @24
    @25
    cA
    wceq
    #
    @26
    @17
    @15
    @4
    @27
    @16
    @23
    @21
    @15
    @4
    wa
    @25
    cA
    cA
    cin
    cA
    @12
    cA
    @3
    cA
    ineq12
    cA
    inidm
    syl6eq
    syl2anb
    @25
    cvv
    wcel
    @26
    @27
    wb
    @12
    @3
    @22
    inex1
    vx
    @25
    cA
    cvv
    eqsbc3
    ax-mp
    sylibr
    a1i
    isfild
end
