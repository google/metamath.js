include "cpr.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "elpri.mm"
include "eqtr3.mm"
include "eqneqall.mm"
include "syl.mm"
include "adantld.mm"
include "ex.mm"
include "a1d.mm"
include "impd.mm"
include "2a1d.mm"
include "jaoi.mm"
include "com12.mm"
include "com13.mm"
include "3imp.mm"
include "syl3an.mm"
include "imp.mm"

theorem 3elpr2eq
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y
  let cZ: class Z


  assert |- ( ( ( X e. { A , B } /\ Y e. { A , B } /\ Z e. { A , B } ) /\ ( Y =/= X /\ Z =/= X ) ) -> Y = Z )

  proof
    cX
    cA
    cB
    cpr
    #
    wcel
    #
    cY
    @0
    wcel
    #
    cZ
    @0
    wcel
    #
    w3a
    cY
    cX
    wne
    #
    cZ
    cX
    wne
    #
    wa
    #
    cY
    cZ
    wceq
    #
    @1
    cX
    cA
    wceq
    #
    cX
    cB
    wceq
    #
    wo
    #
    @2
    cY
    cA
    wceq
    #
    cY
    cB
    wceq
    #
    wo
    #
    @3
    cZ
    cA
    wceq
    #
    cZ
    cB
    wceq
    #
    wo
    #
    @6
    @7
    wi
    #
    cX
    cA
    cB
    elpri
    cY
    cA
    cB
    elpri
    cZ
    cA
    cB
    elpri
    @10
    @13
    @16
    @17
    @8
    @13
    @16
    @17
    wi
    wi
    @9
    @16
    @13
    @8
    @17
    @14
    @13
    @8
    @17
    wi
    #
    wi
    @15
    @14
    @18
    @13
    @14
    @8
    @17
    @14
    @8
    wa
    #
    @5
    @7
    @4
    @19
    cZ
    cX
    wceq
    #
    @5
    @7
    wi
    #
    cZ
    cX
    cA
    eqtr3
    @7
    cZ
    cX
    eqneqall
    #
    syl
    adantld
    ex
    a1d
    @13
    @15
    @18
    @11
    @15
    @18
    wi
    @12
    @11
    @18
    @15
    @11
    @8
    @17
    @11
    @8
    wa
    #
    @4
    @5
    @7
    @23
    cY
    cX
    wceq
    #
    @4
    @21
    wi
    #
    cY
    cX
    cA
    eqtr3
    @21
    cY
    cX
    eqneqall
    #
    syl
    impd
    ex
    a1d
    @12
    @15
    @18
    @12
    @15
    wa
    @7
    @8
    @6
    cY
    cZ
    cB
    eqtr3
    2a1d
    ex
    jaoi
    com12
    jaoi
    com13
    @16
    @13
    @9
    @17
    @14
    @13
    @9
    @17
    wi
    #
    wi
    @15
    @13
    @14
    @27
    @11
    @14
    @27
    wi
    @12
    @11
    @14
    @27
    @11
    @14
    wa
    @7
    @9
    @6
    cY
    cZ
    cA
    eqtr3
    2a1d
    ex
    @12
    @27
    @14
    @12
    @9
    @17
    @12
    @9
    wa
    #
    @4
    @5
    @7
    @28
    @24
    @25
    cY
    cX
    cB
    eqtr3
    @26
    syl
    impd
    ex
    a1d
    jaoi
    com12
    @15
    @27
    @13
    @15
    @9
    @17
    @15
    @9
    wa
    #
    @5
    @7
    @4
    @29
    @20
    @21
    cZ
    cX
    cB
    eqtr3
    @22
    syl
    adantld
    ex
    a1d
    jaoi
    com13
    jaoi
    3imp
    syl3an
    imp
end
