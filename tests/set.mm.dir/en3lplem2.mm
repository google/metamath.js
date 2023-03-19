include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "ctp.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "en3lplem1.mm"
include "3comr.mm"
include "a1d.mm"
include "tprot.mm"
include "ineq2i.mm"
include "neeq1i.mm"
include "bicomi.mm"
include "syl8ib.mm"
include "jao.mm"
include "sylsyld.mm"
include "imp.mm"
include "3coml.mm"
include "w3o.mm"
include "cab.mm"
include "idd.mm"
include "dftp2.mm"
include "eleq2i.mm"
include "syl6ib.mm"
include "abid.mm"
include "df-3or.mm"
include "mpjaod.mm"
include "ex.mm"

theorem en3lplem2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint B x
  disjoint C x
  assert |- ( ( A e. B /\ B e. C /\ C e. A ) -> ( x e. { A , B , C } -> ( x i^i { A , B , C } ) =/= (/) ) )

  proof
    cA
    cB
    wcel
    #
    cB
    cC
    wcel
    #
    cC
    cA
    wcel
    #
    w3a
    #
    vx
    cv
    #
    cA
    cB
    cC
    ctp
    #
    wcel
    #
    @4
    @5
    cin
    #
    c0
    wne
    #
    @3
    @6
    wa
    @4
    cA
    wceq
    #
    @4
    cB
    wceq
    #
    wo
    #
    @8
    @4
    cC
    wceq
    #
    @3
    @6
    @11
    @8
    wi
    #
    @3
    @9
    @8
    wi
    @6
    @10
    @8
    wi
    @13
    vx
    cA
    cB
    cC
    en3lplem1
    @3
    @6
    @10
    @4
    cB
    cC
    cA
    ctp
    #
    cin
    #
    c0
    wne
    #
    @8
    @3
    @10
    @16
    wi
    #
    @6
    @1
    @2
    @0
    @17
    vx
    cB
    cC
    cA
    en3lplem1
    3comr
    a1d
    @8
    @16
    @7
    @15
    c0
    @5
    @14
    @4
    cA
    cB
    cC
    tprot
    ineq2i
    neeq1i
    bicomi
    syl8ib
    @9
    @8
    @10
    jao
    sylsyld
    imp
    @3
    @6
    @12
    @8
    wi
    @3
    @6
    @12
    @4
    cC
    cA
    cB
    ctp
    #
    cin
    #
    c0
    wne
    #
    @8
    @3
    @12
    @20
    wi
    #
    @6
    @2
    @0
    @1
    @21
    vx
    cC
    cA
    cB
    en3lplem1
    3coml
    a1d
    @19
    @7
    c0
    @18
    @5
    @4
    cC
    cA
    cB
    tprot
    ineq2i
    neeq1i
    syl8ib
    imp
    @3
    @6
    @11
    @12
    wo
    #
    @3
    @6
    @9
    @10
    @12
    w3o
    #
    @22
    @3
    @6
    @4
    @23
    vx
    cab
    #
    wcel
    #
    @23
    @3
    @6
    @6
    @25
    @3
    @6
    idd
    @5
    @24
    @4
    vx
    cA
    cB
    cC
    dftp2
    eleq2i
    syl6ib
    @23
    vx
    abid
    syl6ib
    @9
    @10
    @12
    df-3or
    syl6ib
    imp
    mpjaod
    ex
end
