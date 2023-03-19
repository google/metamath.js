include "wrex.mm"
include "wral.mm"
include "wsb.mm"
include "cv.mm"
include "wf.mm"
include "wa.mm"
include "wex.mm"
include "cbvrexsv.mm"
include "ralbii.mm"
include "cfv.mm"
include "sbhypf.mm"
include "ac6s.mm"
include "sylbi.mm"

theorem ac6sf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vz: setvar z
  assume ac6sf.1: |- F/ y ps
  assume ac6sf.2: |- A e. _V
  assume ac6sf.3: |- ( y = ( f ` x ) -> ( ph <-> ps ) )

  disjoint f x
  disjoint A f
  disjoint A x
  disjoint x y
  disjoint B x
  disjoint f y
  disjoint B y
  disjoint B f
  disjoint f ph
  disjoint f z
  disjoint x z
  disjoint A z
  disjoint y z
  disjoint B z
  disjoint ph z
  disjoint ps z
  assert |- ( A. x e. A E. y e. B ph -> E. f ( f : A --> B /\ A. x e. A ps ) )

  proof
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wral
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
    @0
    @2
    vx
    cA
    wph
    vy
    vz
    cB
    cbvrexsv
    ralbii
    @1
    wps
    vx
    vz
    cA
    cB
    vf
    ac6sf.2
    wph
    wps
    vy
    vz
    vx
    cv
    @3
    cfv
    ac6sf.1
    ac6sf.3
    sbhypf
    ac6s
    sylbi
end
