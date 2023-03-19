include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "notbid.mm"
include "ralxfr2d.mm"
include "dfrex2.mm"
include "3bitr4g.mm"

theorem rexxfr2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume ralxfr2d.1: |- ( ( ph /\ y e. C ) -> A e. V )
  assume ralxfr2d.2: |- ( ph -> ( x e. B <-> E. y e. C x = A ) )
  assume ralxfr2d.3: |- ( ( ph /\ x = A ) -> ( ps <-> ch ) )

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint ch x
  disjoint ph x
  disjoint ph y
  disjoint ps y
  assert |- ( ph -> ( E. x e. B ps <-> E. y e. C ch ) )

  proof
    wph
    wps
    wn
    #
    vx
    cB
    wral
    #
    wn
    wch
    wn
    #
    vy
    cC
    wral
    #
    wn
    wps
    vx
    cB
    wrex
    wch
    vy
    cC
    wrex
    wph
    @1
    @3
    wph
    @0
    @2
    vx
    vy
    cA
    cB
    cC
    cV
    ralxfr2d.1
    ralxfr2d.2
    wph
    vx
    cv
    cA
    wceq
    wa
    wps
    wch
    ralxfr2d.3
    notbid
    ralxfr2d
    notbid
    wps
    vx
    cB
    dfrex2
    wch
    vy
    cC
    dfrex2
    3bitr4g
end
