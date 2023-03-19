include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "2wlkdlem6.mm"
include "elfvex.mm"
include "anim12i.mm"
include "syl.mm"

theorem 2wlkdlem7
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


  assert |- ( ph -> ( J e. _V /\ K e. _V ) )

  proof
    wph
    cB
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
    wa
    cJ
    cvv
    wcel
    #
    cK
    cvv
    wcel
    #
    wa
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
    2wlkdlem6
    @0
    @2
    @1
    @3
    cB
    cJ
    cI
    elfvex
    cB
    cK
    cI
    elfvex
    anim12i
    syl
end
