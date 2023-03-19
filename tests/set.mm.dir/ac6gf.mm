include "wrex.mm"
include "wral.mm"
include "wcel.mm"
include "wsb.mm"
include "cv.mm"
include "wf.mm"
include "wa.mm"
include "wex.mm"
include "cbvrexsv.mm"
include "ralbii.mm"
include "cfv.mm"
include "sbhypf.mm"
include "ac6sg.mm"
include "imp.mm"
include "sylan2b.mm"

theorem ac6gf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vz: setvar z
  assume ac6gf.1: |- F/ y ps
  assume ac6gf.2: |- ( y = ( f ` x ) -> ( ph <-> ps ) )

  disjoint A x
  disjoint A y
  disjoint A f
  disjoint x y
  disjoint f x
  disjoint f y
  disjoint B x
  disjoint B y
  disjoint B f
  disjoint f ph
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint f z
  disjoint B z
  disjoint ph z
  disjoint ps z
  assert |- ( ( A e. C /\ A. x e. A E. y e. B ph ) -> E. f ( f : A --> B /\ A. x e. A ps ) )

  proof
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    cA
    cC
    wcel
    #
    wph
    vy
    vz
    wsb
    #
    vz
    cB
    wrex
    #
    vx
    cA
    wral
    #
    cA
    cB
    vf
    cv
    #
    wf
    wps
    vx
    cA
    wral
    wa
    vf
    wex
    #
    @0
    @3
    vx
    cA
    wph
    vy
    vz
    cB
    cbvrexsv
    ralbii
    @1
    @4
    @6
    @2
    wps
    vx
    vz
    cA
    cB
    vf
    cC
    wph
    wps
    vy
    vz
    vx
    cv
    @5
    cfv
    ac6gf.1
    ac6gf.2
    sbhypf
    ac6sg
    imp
    sylan2b
end
