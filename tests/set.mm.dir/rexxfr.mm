include "wrex.mm"
include "wn.mm"
include "wral.mm"
include "dfrex2.mm"
include "cv.mm"
include "wceq.mm"
include "notbid.mm"
include "ralxfr.mm"
include "xchbinxr.mm"
include "bitr4i.mm"

theorem rexxfr
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
  assert |- ( E. x e. B ph <-> E. y e. C ps )

  proof
    wph
    vx
    cB
    wrex
    wph
    wn
    #
    vx
    cB
    wral
    #
    wn
    wps
    vy
    cC
    wrex
    #
    wph
    vx
    cB
    dfrex2
    @2
    wps
    wn
    #
    vy
    cC
    wral
    @1
    wps
    vy
    cC
    dfrex2
    @0
    @3
    vx
    vy
    cA
    cB
    cC
    ralxfr.1
    ralxfr.2
    vx
    cv
    cA
    wceq
    wph
    wps
    ralxfr.3
    notbid
    ralxfr
    xchbinxr
    bitr4i
end
