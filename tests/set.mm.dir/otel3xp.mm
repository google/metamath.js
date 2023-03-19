include "cotp.mm"
include "wceq.mm"
include "wcel.mm"
include "w3a.mm"
include "cxp.mm"
include "cop.mm"
include "df-ot.mm"
include "wa.mm"
include "3simpa.mm"
include "opelxp.mm"
include "sylibr.mm"
include "simp3.mm"
include "opelxpd.mm"
include "syl5eqel.mm"
include "eleq1.mm"
include "syl5ibr.mm"
include "imp.mm"

theorem otel3xp
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  let cX: class X
  let cY: class Y
  let cZ: class Z


  assert |- ( ( T = <. A , B , C >. /\ ( A e. X /\ B e. Y /\ C e. Z ) ) -> T e. ( ( X X. Y ) X. Z ) )

  proof
    cT
    cA
    cB
    cC
    cotp
    #
    wceq
    #
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    cC
    cZ
    wcel
    #
    w3a
    #
    cT
    cX
    cY
    cxp
    #
    cZ
    cxp
    #
    wcel
    #
    @5
    @8
    @1
    @0
    @7
    wcel
    @5
    @0
    cA
    cB
    cop
    #
    cC
    cop
    @7
    cA
    cB
    cC
    df-ot
    @5
    @9
    cC
    @6
    cZ
    @5
    @2
    @3
    wa
    @9
    @6
    wcel
    @2
    @3
    @4
    3simpa
    cA
    cB
    cX
    cY
    opelxp
    sylibr
    @2
    @3
    @4
    simp3
    opelxpd
    syl5eqel
    cT
    @0
    @7
    eleq1
    syl5ibr
    imp
end
