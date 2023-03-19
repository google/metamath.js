include "cc0.mm"
include "cneg.mm"
include "co.mm"
include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "sigarac.mm"
include "syl.mm"
include "eqtr3d.mm"
include "negeqd.mm"
include "neg0.mm"
include "a1i.mm"
include "ancomd.mm"
include "sigarimcd.mm"
include "negnegd.mm"
include "3eqtr3rd.mm"

theorem sigariz
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cG: class G
  let vk: setvar k
  assume sigarimcd.sigar: |- G = ( x e. CC , y e. CC |-> ( Im ` ( ( * ` x ) x. y ) ) )
  assume sigarimcd.a: |- ( ph -> ( A e. CC /\ B e. CC ) )
  assume sigariz.a: |- ( ph -> ( A G B ) = 0 )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint k x
  assert |- ( ph -> ( B G A ) = 0 )

  proof
    wph
    cc0
    cneg
    #
    cB
    cA
    cG
    co
    #
    cneg
    #
    cneg
    cc0
    @1
    wph
    cc0
    @2
    wph
    cA
    cB
    cG
    co
    #
    cc0
    @2
    sigariz.a
    wph
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    @3
    @2
    wceq
    sigarimcd.a
    vx
    vy
    cA
    cB
    cG
    sigarimcd.sigar
    sigarac
    syl
    eqtr3d
    negeqd
    @0
    cc0
    wceq
    wph
    neg0
    a1i
    wph
    @1
    wph
    vx
    vy
    cB
    cA
    cG
    sigarimcd.sigar
    wph
    @4
    @5
    sigarimcd.a
    ancomd
    sigarimcd
    negnegd
    3eqtr3rd
end
