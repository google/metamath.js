include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cs3.mm"
include "wceq.mm"
include "cs2.mm"
include "cs1.mm"
include "s3eqs2s1eq.mm"
include "wb.mm"
include "3simpa.mm"
include "s2eq2seq.mm"
include "syl2an.mm"
include "simp3.mm"
include "s111.mm"
include "anbi12d.mm"
include "df-3an.mm"
include "syl6bbr.mm"
include "bitrd.mm"

theorem s3eq3seq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cV: class V


  assert |- ( ( ( A e. V /\ B e. V /\ C e. V ) /\ ( D e. V /\ E e. V /\ F e. V ) ) -> ( <" A B C "> = <" D E F "> <-> ( A = D /\ B = E /\ C = F ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    w3a
    #
    cD
    cV
    wcel
    #
    cE
    cV
    wcel
    #
    cF
    cV
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cB
    cC
    cs3
    cD
    cE
    cF
    cs3
    wceq
    cA
    cB
    cs2
    cD
    cE
    cs2
    wceq
    #
    cC
    cs1
    cF
    cs1
    wceq
    #
    wa
    #
    cA
    cD
    wceq
    #
    cB
    cE
    wceq
    #
    cC
    cF
    wceq
    #
    w3a
    #
    cA
    cB
    cC
    cD
    cE
    cF
    cV
    s3eqs2s1eq
    @8
    @11
    @12
    @13
    wa
    #
    @14
    wa
    @15
    @8
    @9
    @16
    @10
    @14
    @3
    @0
    @1
    wa
    @4
    @5
    wa
    @9
    @16
    wb
    @7
    @0
    @1
    @2
    3simpa
    @4
    @5
    @6
    3simpa
    cA
    cB
    cD
    cE
    cV
    s2eq2seq
    syl2an
    @3
    @2
    @6
    @10
    @14
    wb
    @7
    @0
    @1
    @2
    simp3
    @4
    @5
    @6
    simp3
    cV
    cC
    cF
    s111
    syl2an
    anbi12d
    @12
    @13
    @14
    df-3an
    syl6bbr
    bitrd
end
