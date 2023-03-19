include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "c2.mm"
include "c3.mm"
include "cs4.mm"
include "fveq1i.mm"
include "s4fv0.mm"
include "syl5eq.mm"
include "s4fv1.mm"
include "anim12i.mm"
include "s4fv2.mm"
include "s4fv3.mm"
include "syl.mm"

theorem 3wlkdlem3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let cV: class V
  let vk: setvar k
  assume 3wlkd.p: |- P = <" A B C D ">
  assume 3wlkd.f: |- F = <" J K L ">
  assume 3wlkd.s: |- ( ph -> ( ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) )


  assert |- ( ph -> ( ( ( P ` 0 ) = A /\ ( P ` 1 ) = B ) /\ ( ( P ` 2 ) = C /\ ( P ` 3 ) = D ) ) )

  proof
    wph
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    wa
    #
    cC
    cV
    wcel
    #
    cD
    cV
    wcel
    #
    wa
    #
    wa
    cc0
    cP
    cfv
    #
    cA
    wceq
    #
    c1
    cP
    cfv
    #
    cB
    wceq
    #
    wa
    #
    c2
    cP
    cfv
    #
    cC
    wceq
    #
    c3
    cP
    cfv
    #
    cD
    wceq
    #
    wa
    #
    wa
    3wlkd.s
    @2
    @10
    @5
    @15
    @0
    @7
    @1
    @9
    @0
    @6
    cc0
    cA
    cB
    cC
    cD
    cs4
    #
    cfv
    cA
    cc0
    cP
    @16
    3wlkd.p
    fveq1i
    cA
    cB
    cC
    cD
    cV
    s4fv0
    syl5eq
    @1
    @8
    c1
    @16
    cfv
    cB
    c1
    cP
    @16
    3wlkd.p
    fveq1i
    cA
    cB
    cC
    cD
    cV
    s4fv1
    syl5eq
    anim12i
    @3
    @12
    @4
    @14
    @3
    @11
    c2
    @16
    cfv
    cC
    c2
    cP
    @16
    3wlkd.p
    fveq1i
    cA
    cB
    cC
    cD
    cV
    s4fv2
    syl5eq
    @4
    @13
    c3
    @16
    cfv
    cD
    c3
    cP
    @16
    3wlkd.p
    fveq1i
    cA
    cB
    cC
    cD
    cV
    s4fv3
    syl5eq
    anim12i
    anim12i
    syl
end
