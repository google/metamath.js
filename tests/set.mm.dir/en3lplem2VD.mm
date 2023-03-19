include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "ctp.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wceq.mm"
include "wo.mm"
include "idn1.mm"
include "idn3.mm"
include "en3lplem1VD.mm"
include "e13.mm"
include "in3.mm"
include "3anrot.mm"
include "e1bi.mm"
include "tprot.mm"
include "eleq2i.mm"
include "anbi1i.mm"
include "exbii.mm"
include "e3bir.mm"
include "jao.mm"
include "e22.mm"
include "e1bir.mm"
include "e3bi.mm"
include "w3o.mm"
include "cab.mm"
include "idn2.mm"
include "dftp2.mm"
include "e2bi.mm"
include "abid.mm"
include "df-3or.mm"
include "e222.mm"
include "in2.mm"
include "in1.mm"

theorem en3lplem2VD
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ( A e. B /\ B e. C /\ C e. A ) -> ( x e. { A , B , C } -> E. y ( y e. { A , B , C } /\ y e. x ) ) )

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
    vy
    cv
    #
    @5
    wcel
    #
    @7
    @4
    wcel
    #
    wa
    #
    vy
    wex
    #
    wi
    @3
    @6
    @11
    @3
    @6
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
    @11
    wi
    #
    @4
    cC
    wceq
    #
    @11
    wi
    @14
    @16
    wo
    #
    @11
    @3
    @6
    @12
    @11
    wi
    @13
    @11
    wi
    @15
    @3
    @6
    @12
    @11
    @3
    @3
    @6
    @12
    @12
    @11
    @3
    idn1
    #
    @3
    @6
    @12
    idn3
    vx
    vy
    cA
    cB
    cC
    en3lplem1VD
    e13
    in3
    @3
    @6
    @13
    @11
    @3
    @6
    @13
    @7
    cB
    cC
    cA
    ctp
    #
    wcel
    #
    @9
    wa
    #
    vy
    wex
    #
    @11
    @3
    @1
    @2
    @0
    w3a
    #
    @6
    @13
    @13
    @22
    @3
    @3
    @23
    @18
    @0
    @1
    @2
    3anrot
    e1bi
    @3
    @6
    @13
    idn3
    vx
    vy
    cB
    cC
    cA
    en3lplem1VD
    e13
    @10
    @21
    vy
    @8
    @20
    @9
    @5
    @19
    @7
    cA
    cB
    cC
    tprot
    eleq2i
    anbi1i
    exbii
    e3bir
    in3
    @12
    @11
    @13
    jao
    e22
    @3
    @6
    @16
    @11
    @3
    @6
    @16
    @7
    cC
    cA
    cB
    ctp
    #
    wcel
    #
    @9
    wa
    #
    vy
    wex
    #
    @11
    @3
    @2
    @0
    @1
    w3a
    #
    @6
    @16
    @16
    @27
    @3
    @3
    @28
    @18
    @2
    @0
    @1
    3anrot
    e1bir
    @3
    @6
    @16
    idn3
    vx
    vy
    cC
    cA
    cB
    en3lplem1VD
    e13
    @26
    @10
    vy
    @25
    @8
    @9
    @24
    @5
    @7
    cC
    cA
    cB
    tprot
    eleq2i
    anbi1i
    exbii
    e3bi
    in3
    @3
    @6
    @12
    @13
    @16
    w3o
    #
    @17
    @3
    @6
    @4
    @29
    vx
    cab
    #
    wcel
    #
    @29
    @3
    @6
    @6
    @31
    @3
    @6
    idn2
    @5
    @30
    @4
    vx
    cA
    cB
    cC
    dftp2
    eleq2i
    e2bi
    @29
    vx
    abid
    e2bi
    @12
    @13
    @16
    df-3or
    e2bi
    @14
    @11
    @16
    jao
    e222
    in2
    in1
end
