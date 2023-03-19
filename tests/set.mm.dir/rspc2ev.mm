include "wcel.mm"
include "w3a.mm"
include "wrex.mm"
include "wa.mm"
include "rspcev.mm"
include "anim2i.mm"
include "3impb.mm"
include "cv.mm"
include "wceq.mm"
include "rexbidv.mm"
include "syl.mm"

theorem rspc2ev
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume rspc2v.1: |- ( x = A -> ( ph <-> ch ) )
  assume rspc2v.2: |- ( y = B -> ( ch <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint D x
  disjoint D y
  disjoint ch x
  disjoint ps y
  assert |- ( ( A e. C /\ B e. D /\ ps ) -> E. x e. C E. y e. D ph )

  proof
    cA
    cC
    wcel
    #
    cB
    cD
    wcel
    #
    wps
    w3a
    @0
    wch
    vy
    cD
    wrex
    #
    wa
    #
    wph
    vy
    cD
    wrex
    #
    vx
    cC
    wrex
    @0
    @1
    wps
    @3
    @1
    wps
    wa
    @2
    @0
    wch
    wps
    vy
    cB
    cD
    rspc2v.2
    rspcev
    anim2i
    3impb
    @4
    @2
    vx
    cA
    cC
    vx
    cv
    cA
    wceq
    wph
    wch
    vy
    cD
    rspc2v.1
    rexbidv
    rspcev
    syl
end
