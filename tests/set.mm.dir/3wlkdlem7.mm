include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cvv.mm"
include "3wlkdlem6.mm"
include "elfvex.mm"
include "3anim123i.mm"
include "syl.mm"

theorem 3wlkdlem7
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


  assert |- ( ph -> ( J e. _V /\ K e. _V /\ L e. _V ) )

  proof
    wph
    cA
    cJ
    cI
    cfv
    wcel
    #
    cB
    cK
    cI
    cfv
    wcel
    #
    cC
    cL
    cI
    cfv
    wcel
    #
    w3a
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
    3wlkdlem6
    @0
    @3
    @1
    @4
    @2
    @5
    cA
    cJ
    cI
    elfvex
    cB
    cK
    cI
    elfvex
    cC
    cL
    cI
    elfvex
    3anim123i
    syl
end
