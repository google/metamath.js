include "wa.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "simpl.mm"
include "ralimi.mm"
include "weq.mm"
include "biidd.mm"
include "rspcv.mm"
include "syl5.mm"
include "wi.mm"
include "simpr.mm"
include "a1i.mm"
include "jcad.mm"
include "ralimia.mm"
include "r19.28v.mm"
include "impbii.mm"

theorem rr19.28v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint A y
  disjoint x y
  disjoint ph y
  assert |- ( A. x e. A A. y e. A ( ph /\ ps ) <-> A. x e. A ( ph /\ A. y e. A ps ) )

  proof
    wph
    wps
    wa
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    wph
    wps
    vy
    cA
    wral
    #
    wa
    #
    vx
    cA
    wral
    @1
    @3
    vx
    cA
    vx
    cv
    #
    cA
    wcel
    #
    @1
    wph
    @2
    @1
    wph
    vy
    cA
    wral
    @5
    wph
    @0
    wph
    vy
    cA
    wph
    wps
    simpl
    ralimi
    wph
    wph
    vy
    @4
    cA
    vy
    vx
    weq
    wph
    biidd
    rspcv
    syl5
    @1
    @2
    wi
    @5
    @0
    wps
    vy
    cA
    wph
    wps
    simpr
    ralimi
    a1i
    jcad
    ralimia
    @3
    @1
    vx
    cA
    wph
    wps
    vy
    cA
    r19.28v
    ralimi
    impbii
end
