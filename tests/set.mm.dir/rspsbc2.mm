include "wcel.mm"
include "wral.mm"
include "wsbc.mm"
include "idd.mm"
include "wi.mm"
include "rspsbc.mm"
include "a1d.mm"
include "sbcralg.mm"
include "biimpd.mm"
include "syl6d.mm"
include "syl10.mm"

theorem rspsbc2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D

  disjoint A y
  disjoint B x
  disjoint D x
  disjoint D y
  disjoint x y
  assert |- ( A e. B -> ( C e. D -> ( A. x e. B A. y e. D ph -> [. C / y ]. [. A / x ]. ph ) ) )

  proof
    cA
    cB
    wcel
    #
    cC
    cD
    wcel
    #
    @1
    wph
    vy
    cD
    wral
    #
    vx
    cB
    wral
    #
    wph
    vx
    cA
    wsbc
    #
    vy
    cD
    wral
    #
    @4
    vy
    cC
    wsbc
    @0
    @1
    idd
    @0
    @1
    @3
    @2
    vx
    cA
    wsbc
    #
    @5
    @0
    @3
    @6
    wi
    @1
    @2
    vx
    cA
    cB
    rspsbc
    a1d
    @0
    @6
    @5
    wph
    vx
    vy
    cA
    cD
    cB
    sbcralg
    biimpd
    syl6d
    @4
    vy
    cC
    cD
    rspsbc
    syl10
end
