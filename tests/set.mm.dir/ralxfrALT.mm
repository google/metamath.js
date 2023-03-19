include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "rspcv.mm"
include "syl.mm"
include "com12.mm"
include "ralrimiv.mm"
include "wceq.mm"
include "wrex.mm"
include "nfra1.mm"
include "nfv.mm"
include "rsp.mm"
include "biimprcd.mm"
include "syl6.mm"
include "rexlimd.mm"
include "syl5.mm"
include "impbii.mm"

theorem ralxfrALT
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume ralxfr.1: |- ( y e. C -> A e. B )
  assume ralxfr.2: |- ( x e. B -> E. y e. C x = A )
  assume ralxfr.3: |- ( x = A -> ( ph <-> ps ) )

  disjoint ps x
  disjoint ph y
  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  assert |- ( A. x e. B ph <-> A. y e. C ps )

  proof
    wph
    vx
    cB
    wral
    #
    wps
    vy
    cC
    wral
    #
    @0
    wps
    vy
    cC
    vy
    cv
    cC
    wcel
    #
    @0
    wps
    @2
    cA
    cB
    wcel
    @0
    wps
    wi
    ralxfr.1
    wph
    wps
    vx
    cA
    cB
    ralxfr.3
    rspcv
    syl
    com12
    ralrimiv
    @1
    wph
    vx
    cB
    vx
    cv
    #
    cB
    wcel
    @3
    cA
    wceq
    #
    vy
    cC
    wrex
    @1
    wph
    ralxfr.2
    @1
    @4
    wph
    vy
    cC
    wps
    vy
    cC
    nfra1
    wph
    vy
    nfv
    @1
    @2
    wps
    @4
    wph
    wi
    wps
    vy
    cC
    rsp
    @4
    wph
    wps
    ralxfr.3
    biimprcd
    syl6
    rexlimd
    syl5
    ralrimiv
    impbii
end
