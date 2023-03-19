include "cc0.mm"
include "cs2.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cvv.mm"
include "wcel.mm"
include "2wlkdlem7.mm"
include "s2fv0.mm"
include "s2fv1.mm"
include "anim12i.mm"
include "syl.mm"
include "fveq1i.mm"
include "eqeq1i.mm"
include "anbi12i.mm"
include "sylibr.mm"

theorem 2wlkdlem8
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cF: class F
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let vk: setvar k
  let vj: setvar j
  assume 2wlkd.p: |- P = <" A B C ">
  assume 2wlkd.f: |- F = <" J K ">
  assume 2wlkd.s: |- ( ph -> ( A e. V /\ B e. V /\ C e. V ) )
  assume 2wlkd.n: |- ( ph -> ( A =/= B /\ B =/= C ) )
  assume 2wlkd.e: |- ( ph -> ( { A , B } C_ ( I ` J ) /\ { B , C } C_ ( I ` K ) ) )


  assert |- ( ph -> ( ( F ` 0 ) = J /\ ( F ` 1 ) = K ) )

  proof
    wph
    cc0
    cJ
    cK
    cs2
    #
    cfv
    #
    cJ
    wceq
    #
    c1
    @0
    cfv
    #
    cK
    wceq
    #
    wa
    #
    cc0
    cF
    cfv
    #
    cJ
    wceq
    #
    c1
    cF
    cfv
    #
    cK
    wceq
    #
    wa
    wph
    cJ
    cvv
    wcel
    #
    cK
    cvv
    wcel
    #
    wa
    @5
    wph
    cA
    cB
    cC
    cP
    cF
    cI
    cJ
    cK
    cV
    2wlkd.p
    2wlkd.f
    2wlkd.s
    2wlkd.n
    2wlkd.e
    2wlkdlem7
    @10
    @2
    @11
    @4
    cJ
    cK
    cvv
    s2fv0
    cJ
    cK
    cvv
    s2fv1
    anim12i
    syl
    @7
    @2
    @9
    @4
    @6
    @1
    cJ
    cc0
    cF
    @0
    2wlkd.f
    fveq1i
    eqeq1i
    @8
    @3
    cK
    c1
    cF
    @0
    2wlkd.f
    fveq1i
    eqeq1i
    anbi12i
    sylibr
end
