include "cr1.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "wa.mm"
include "crnk.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wceq.mm"
include "wlim.mm"
include "word.mm"
include "wi.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpri.mm"
include "limord.mm"
include "ordtr1.mm"
include "mp2b.mm"
include "ancoms.mm"
include "rankonidlem.mm"
include "syl.mm"
include "simprd.mm"
include "simpr.mm"
include "eqeltrd.mm"
include "wb.mm"
include "simpld.mm"
include "simpl.mm"
include "rankr1ag.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ex.mm"
include "ssrdv.mm"

theorem onssr1
  let cA: class A
  let vx: setvar x


  assert |- ( A e. dom R1 -> A C_ ( R1 ` A ) )

  proof
    cA
    cr1
    cdm
    #
    wcel
    #
    vx
    cA
    cA
    cr1
    cfv
    #
    @1
    vx
    cv
    #
    cA
    wcel
    #
    @3
    @2
    wcel
    #
    @1
    @4
    wa
    #
    @5
    @3
    crnk
    cfv
    #
    cA
    wcel
    #
    @6
    @7
    @3
    cA
    @6
    @3
    cr1
    con0
    cima
    cuni
    wcel
    #
    @7
    @3
    wceq
    #
    @6
    @3
    @0
    wcel
    #
    @9
    @10
    wa
    @4
    @1
    @11
    @0
    wlim
    #
    @0
    word
    @4
    @1
    wa
    @11
    wi
    cr1
    wfun
    @12
    r1funlim
    simpri
    @0
    limord
    @3
    cA
    @0
    ordtr1
    mp2b
    ancoms
    @3
    rankonidlem
    syl
    #
    simprd
    @1
    @4
    simpr
    eqeltrd
    @6
    @9
    @1
    @5
    @8
    wb
    @6
    @9
    @10
    @13
    simpld
    @1
    @4
    simpl
    @3
    cA
    rankr1ag
    syl2anc
    mpbird
    ex
    ssrdv
end
