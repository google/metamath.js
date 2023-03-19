include "csur.mm"
include "wcel.mm"
include "cslt.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "wa.mm"
include "c1o.mm"
include "c0.mm"
include "cop.mm"
include "c2o.mm"
include "ctp.mm"
include "sltval2.mm"
include "wceq.mm"
include "w3o.mm"
include "fvex.mm"
include "brtp.mm"
include "1n0.mm"
include "simpl.mm"
include "simpr.mm"
include "neeq12d.mm"
include "mpbiri.mm"
include "csuc.mm"
include "df-2o.mm"
include "df-1o.mm"
include "eqeq12i.mm"
include "wb.mm"
include "1on.mm"
include "0elon.mm"
include "suc11.mm"
include "mp2an.mm"
include "bitri.mm"
include "necon3bii.mm"
include "mpbir.mm"
include "necomi.mm"
include "2on.mm"
include "elexi.mm"
include "prid2.mm"
include "nosgnn0i.mm"
include "3jaoi.mm"
include "sylbi.mm"
include "syl6bi.mm"
include "3impia.mm"

theorem nosepnelem
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. No /\ B e. No /\ A <s B ) -> ( A ` |^| { x e. On | ( A ` x ) =/= ( B ` x ) } ) =/= ( B ` |^| { x e. On | ( A ` x ) =/= ( B ` x ) } ) )

  proof
    cA
    csur
    wcel
    #
    cB
    csur
    wcel
    #
    cA
    cB
    cslt
    wbr
    #
    vx
    cv
    #
    cA
    cfv
    @3
    cB
    cfv
    wne
    vx
    con0
    crab
    cint
    #
    cA
    cfv
    #
    @4
    cB
    cfv
    #
    wne
    #
    @0
    @1
    wa
    @2
    @5
    @6
    c1o
    c0
    cop
    c1o
    c2o
    cop
    c0
    c2o
    cop
    ctp
    wbr
    #
    @7
    cA
    cB
    vx
    sltval2
    @8
    @5
    c1o
    wceq
    #
    @6
    c0
    wceq
    #
    wa
    #
    @9
    @6
    c2o
    wceq
    #
    wa
    #
    @5
    c0
    wceq
    #
    @12
    wa
    #
    w3o
    @7
    c1o
    c0
    c1o
    c2o
    c0
    c2o
    @5
    @6
    @4
    cA
    fvex
    @4
    cB
    fvex
    brtp
    @11
    @7
    @13
    @15
    @11
    @7
    c1o
    c0
    wne
    #
    1n0
    @11
    @5
    c1o
    @6
    c0
    @9
    @10
    simpl
    @9
    @10
    simpr
    neeq12d
    mpbiri
    @13
    @7
    c1o
    c2o
    wne
    c2o
    c1o
    c2o
    c1o
    wne
    @16
    1n0
    c2o
    c1o
    c1o
    c0
    c2o
    c1o
    wceq
    c1o
    csuc
    #
    c0
    csuc
    #
    wceq
    #
    c1o
    c0
    wceq
    #
    c2o
    @17
    c1o
    @18
    df-2o
    df-1o
    eqeq12i
    c1o
    con0
    wcel
    c0
    con0
    wcel
    @19
    @20
    wb
    1on
    0elon
    c1o
    c0
    suc11
    mp2an
    bitri
    necon3bii
    mpbir
    necomi
    @13
    @5
    c1o
    @6
    c2o
    @9
    @12
    simpl
    @9
    @12
    simpr
    neeq12d
    mpbiri
    @15
    @7
    c0
    c2o
    wne
    c2o
    c1o
    c2o
    c2o
    con0
    2on
    elexi
    prid2
    nosgnn0i
    @15
    @5
    c0
    @6
    c2o
    @14
    @12
    simpl
    @14
    @12
    simpr
    neeq12d
    mpbiri
    3jaoi
    sylbi
    syl6bi
    3impia
end
