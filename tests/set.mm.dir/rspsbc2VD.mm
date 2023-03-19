include "wcel.mm"
include "wral.mm"
include "wsbc.mm"
include "wi.mm"
include "idn2.mm"
include "idn1.mm"
include "idn3.mm"
include "rspsbc.mm"
include "e13.mm"
include "sbcralg.mm"
include "biimpd.mm"
include "e23.mm"
include "in3.mm"
include "in2.mm"
include "in1.mm"

theorem rspsbc2VD
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
    cC
    wsbc
    #
    wi
    #
    wi
    @0
    @1
    @6
    @0
    @1
    @3
    @5
    @0
    @1
    @1
    @3
    @4
    vy
    cD
    wral
    #
    @5
    @0
    @1
    idn2
    @0
    @0
    @1
    @3
    @2
    vx
    cA
    wsbc
    #
    @7
    @0
    idn1
    #
    @0
    @0
    @1
    @3
    @3
    @8
    @9
    @0
    @1
    @3
    idn3
    @2
    vx
    cA
    cB
    rspsbc
    e13
    @0
    @8
    @7
    wph
    vx
    vy
    cA
    cD
    cB
    sbcralg
    biimpd
    e13
    @4
    vy
    cC
    cD
    rspsbc
    e23
    in3
    in2
    in1
end
