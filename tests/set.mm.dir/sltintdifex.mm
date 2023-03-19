include "csur.mm"
include "wcel.mm"
include "wa.mm"
include "cslt.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "c1o.mm"
include "c0.mm"
include "cop.mm"
include "c2o.mm"
include "ctp.mm"
include "cvv.mm"
include "sltval2.mm"
include "wceq.mm"
include "w3o.mm"
include "fvex.mm"
include "brtp.mm"
include "wn.mm"
include "fvprc.mm"
include "1n0.mm"
include "neii.mm"
include "eqeq1.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "mtbiri.mm"
include "syl.mm"
include "con4i.mm"
include "adantr.mm"
include "2on0.mm"
include "adantl.mm"
include "3jaoi.mm"
include "sylbi.mm"
include "syl6bi.mm"

theorem sltintdifex
  let cA: class A
  let cB: class B
  let va: setvar a

  disjoint A a
  disjoint B a
  assert |- ( ( A e. No /\ B e. No ) -> ( A <s B -> |^| { a e. On | ( A ` a ) =/= ( B ` a ) } e. _V ) )

  proof
    cA
    csur
    wcel
    cB
    csur
    wcel
    wa
    cA
    cB
    cslt
    wbr
    va
    cv
    #
    cA
    cfv
    @0
    cB
    cfv
    wne
    va
    con0
    crab
    cint
    #
    cA
    cfv
    #
    @1
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
    wbr
    #
    @1
    cvv
    wcel
    #
    cA
    cB
    va
    sltval2
    @4
    @2
    c1o
    wceq
    #
    @3
    c0
    wceq
    #
    wa
    #
    @6
    @3
    c2o
    wceq
    #
    wa
    #
    @2
    c0
    wceq
    #
    @9
    wa
    #
    w3o
    @5
    c1o
    c0
    c1o
    c2o
    c0
    c2o
    @2
    @3
    @1
    cA
    fvex
    @1
    cB
    fvex
    brtp
    @8
    @5
    @10
    @12
    @6
    @5
    @7
    @5
    @6
    @5
    wn
    #
    @11
    @6
    wn
    @1
    cA
    fvprc
    @11
    @6
    c1o
    c0
    wceq
    #
    c1o
    c0
    1n0
    neii
    @11
    @6
    c0
    c1o
    wceq
    @14
    @2
    c0
    c1o
    eqeq1
    c0
    c1o
    eqcom
    syl6bb
    mtbiri
    syl
    con4i
    #
    adantr
    @6
    @5
    @9
    @15
    adantr
    @9
    @5
    @11
    @5
    @9
    @13
    @7
    @9
    wn
    @1
    cB
    fvprc
    @7
    @9
    c2o
    c0
    wceq
    #
    c2o
    c0
    2on0
    neii
    @7
    @9
    c0
    c2o
    wceq
    @16
    @3
    c0
    c2o
    eqeq1
    c0
    c2o
    eqcom
    syl6bb
    mtbiri
    syl
    con4i
    adantl
    3jaoi
    sylbi
    syl6bi
end
