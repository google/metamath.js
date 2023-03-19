include "cc0.mm"
include "cs3.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "c2.mm"
include "w3a.mm"
include "cvv.mm"
include "wcel.mm"
include "3wlkdlem7.mm"
include "s3fv0.mm"
include "s3fv1.mm"
include "s3fv2.mm"
include "3anim123i.mm"
include "syl.mm"
include "fveq1i.mm"
include "eqeq1i.mm"
include "3anbi123i.mm"
include "sylibr.mm"

theorem 3wlkdlem8
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cF: class F
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cV: class V
  let vk: setvar k
  let vj: setvar j
  assume 3wlkd.p: |- P = <" A B C D ">
  assume 3wlkd.f: |- F = <" J K L ">
  assume 3wlkd.s: |- ( ph -> ( ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) )
  assume 3wlkd.n: |- ( ph -> ( ( A =/= B /\ A =/= C ) /\ ( B =/= C /\ B =/= D ) /\ C =/= D ) )
  assume 3wlkd.e: |- ( ph -> ( { A , B } C_ ( I ` J ) /\ { B , C } C_ ( I ` K ) /\ { C , D } C_ ( I ` L ) ) )


  assert |- ( ph -> ( ( F ` 0 ) = J /\ ( F ` 1 ) = K /\ ( F ` 2 ) = L ) )

  proof
    wph
    cc0
    cJ
    cK
    cL
    cs3
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
    c2
    @0
    cfv
    #
    cL
    wceq
    #
    w3a
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
    c2
    cF
    cfv
    #
    cL
    wceq
    #
    w3a
    wph
    cJ
    cvv
    wcel
    #
    cK
    cvv
    wcel
    #
    cL
    cvv
    wcel
    #
    w3a
    @7
    wph
    cA
    cB
    cC
    cD
    cP
    cF
    cI
    cJ
    cK
    cL
    cV
    3wlkd.p
    3wlkd.f
    3wlkd.s
    3wlkd.n
    3wlkd.e
    3wlkdlem7
    @14
    @2
    @15
    @4
    @16
    @6
    cJ
    cK
    cL
    cvv
    s3fv0
    cJ
    cK
    cL
    cvv
    s3fv1
    cJ
    cK
    cL
    cvv
    s3fv2
    3anim123i
    syl
    @9
    @2
    @11
    @4
    @13
    @6
    @8
    @1
    cJ
    cc0
    cF
    @0
    3wlkd.f
    fveq1i
    eqeq1i
    @10
    @3
    cK
    c1
    cF
    @0
    3wlkd.f
    fveq1i
    eqeq1i
    @12
    @5
    cL
    c2
    cF
    @0
    3wlkd.f
    fveq1i
    eqeq1i
    3anbi123i
    sylibr
end
