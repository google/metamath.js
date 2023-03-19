include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "notbid.mm"
include "ralxfrd.mm"
include "dfrex2.mm"
include "3bitr4g.mm"

theorem rexxfrd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume ralxfrd.1: |- ( ( ph /\ y e. C ) -> A e. B )
  assume ralxfrd.2: |- ( ( ph /\ x e. B ) -> E. y e. C x = A )
  assume ralxfrd.3: |- ( ( ph /\ x = A ) -> ( ps <-> ch ) )

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
    ralxfrd.1
    ralxfrd.2
    wph
    vx
    cv
    cA
    wceq
    wa
    wps
    wch
    ralxfrd.3
    notbid
    ralxfrd
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
