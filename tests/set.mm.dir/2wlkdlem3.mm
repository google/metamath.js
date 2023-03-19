include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "c2.mm"
include "cs3.mm"
include "fveq1i.mm"
include "s3fv0.mm"
include "syl5eq.mm"
include "s3fv1.mm"
include "s3fv2.mm"
include "3anim123i.mm"
include "syl.mm"

theorem 2wlkdlem3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cV: class V
  assume 2wlkd.p: |- P = <" A B C ">
  assume 2wlkd.f: |- F = <" J K ">
  assume 2wlkd.s: |- ( ph -> ( A e. V /\ B e. V /\ C e. V ) )


  assert |- ( ph -> ( ( P ` 0 ) = A /\ ( P ` 1 ) = B /\ ( P ` 2 ) = C ) )

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
    cC
    cV
    wcel
    #
    w3a
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
    c2
    cP
    cfv
    #
    cC
    wceq
    #
    w3a
    2wlkd.s
    @0
    @4
    @1
    @6
    @2
    @8
    @0
    @3
    cc0
    cA
    cB
    cC
    cs3
    #
    cfv
    cA
    cc0
    cP
    @9
    2wlkd.p
    fveq1i
    cA
    cB
    cC
    cV
    s3fv0
    syl5eq
    @1
    @5
    c1
    @9
    cfv
    cB
    c1
    cP
    @9
    2wlkd.p
    fveq1i
    cA
    cB
    cC
    cV
    s3fv1
    syl5eq
    @2
    @7
    c2
    @9
    cfv
    cC
    c2
    cP
    @9
    2wlkd.p
    fveq1i
    cA
    cB
    cC
    cV
    s3fv2
    syl5eq
    3anim123i
    syl
end
