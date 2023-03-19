include "csur.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "c1o.mm"
include "wceq.mm"
include "wa.mm"
include "cslt.mm"
include "wbr.mm"
include "c0.mm"
include "cop.mm"
include "c2o.mm"
include "ctp.mm"
include "simpr.mm"
include "w3o.mm"
include "wo.mm"
include "wn.mm"
include "nosepne.mm"
include "adantr.mm"
include "eqnetrrd.mm"
include "necomd.mm"
include "neneqd.mm"
include "simpl2.mm"
include "nofv.mm"
include "syl.mm"
include "3orel2.mm"
include "sylc.mm"
include "eqid.mm"
include "jctil.mm"
include "andi.mm"
include "sylib.mm"
include "3mix1.mm"
include "3mix2.mm"
include "jaoi.mm"
include "1on.mm"
include "elexi.mm"
include "fvex.mm"
include "brtp.mm"
include "sylibr.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "simpl1.mm"
include "sltval2.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem nosep1o
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( ( A e. No /\ B e. No /\ A =/= B ) /\ ( A ` |^| { x e. On | ( A ` x ) =/= ( B ` x ) } ) = 1o ) -> A <s B )

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
    wne
    #
    w3a
    #
    vx
    cv
    #
    cA
    cfv
    @4
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
    c1o
    wceq
    #
    wa
    #
    cA
    cB
    cslt
    wbr
    #
    @6
    @5
    cB
    cfv
    #
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
    #
    wbr
    #
    @8
    @6
    c1o
    @10
    @11
    @3
    @7
    simpr
    #
    @8
    c1o
    c1o
    wceq
    #
    @10
    c0
    wceq
    #
    wa
    #
    @14
    @10
    c2o
    wceq
    #
    wa
    #
    c1o
    c0
    wceq
    @17
    wa
    #
    w3o
    #
    c1o
    @10
    @11
    wbr
    @8
    @16
    @18
    wo
    #
    @20
    @8
    @14
    @15
    @17
    wo
    #
    wa
    @21
    @8
    @22
    @14
    @8
    @10
    c1o
    wceq
    #
    wn
    @15
    @23
    @17
    w3o
    #
    @22
    @8
    @10
    c1o
    @8
    c1o
    @10
    @8
    @6
    c1o
    @10
    @13
    @3
    @6
    @10
    wne
    @7
    vx
    cA
    cB
    nosepne
    adantr
    eqnetrrd
    necomd
    neneqd
    @8
    @1
    @24
    @0
    @1
    @2
    @7
    simpl2
    #
    cB
    @5
    nofv
    syl
    @15
    @23
    @17
    3orel2
    sylc
    c1o
    eqid
    jctil
    @14
    @15
    @17
    andi
    sylib
    @16
    @20
    @18
    @16
    @18
    @19
    3mix1
    @18
    @16
    @19
    3mix2
    jaoi
    syl
    c1o
    c0
    c1o
    c2o
    c0
    c2o
    c1o
    @10
    c1o
    con0
    1on
    elexi
    @5
    cB
    fvex
    brtp
    sylibr
    eqbrtrd
    @8
    @0
    @1
    @9
    @12
    wb
    @0
    @1
    @2
    @7
    simpl1
    @25
    cA
    cB
    vx
    sltval2
    syl2anc
    mpbird
end
