include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "sigarim.mm"
include "recnd.mm"
include "syl.mm"

theorem sigarimcd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cG: class G
  let vk: setvar k
  assume sigarimcd.sigar: |- G = ( x e. CC , y e. CC |-> ( Im ` ( ( * ` x ) x. y ) ) )
  assume sigarimcd.a: |- ( ph -> ( A e. CC /\ B e. CC ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint k x
  assert |- ( ph -> ( A G B ) e. CC )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    wa
    #
    cA
    cB
    cG
    co
    #
    cc
    wcel
    sigarimcd.a
    @0
    @1
    vx
    vy
    cA
    cB
    cG
    sigarimcd.sigar
    sigarim
    recnd
    syl
end
