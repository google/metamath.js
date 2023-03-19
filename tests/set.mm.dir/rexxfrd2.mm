include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "w3a.mm"
include "notbid.mm"
include "ralxfrd2.mm"
include "dfrex2.mm"
include "3bitr4g.mm"

theorem rexxfrd2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume ralxfrd2.1: |- ( ( ph /\ y e. C ) -> A e. B )
  assume ralxfrd2.2: |- ( ( ph /\ x e. B ) -> E. y e. C x = A )
  assume ralxfrd2.3: |- ( ( ph /\ y e. C /\ x = A ) -> ( ps <-> ch ) )

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
    ralxfrd2.1
    ralxfrd2.2
    wph
    vy
    cv
    cC
    wcel
    vx
    cv
    cA
    wceq
    w3a
    wps
    wch
    ralxfrd2.3
    notbid
    ralxfrd2
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
